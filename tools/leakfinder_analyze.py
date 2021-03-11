#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import re

class Trace:
    def __init__(self, count, hash):
        self.count = count
        self.hash = hash
        self.frames = []

    def __lt__(self, other):
        return self.hash < other.hash

    def character(self):
        return hash(tuple(self.frames[4:]))

class Capture:
    def __init__(self):
        self.load()

    def load(self):
        self.table = {}
        for line in open("/tmp/trace-1", "r").readlines():
            mo = re.search("(trace|expanded): count ([-0-9]*).*hash *(.*)", line)
            if mo!=None:
                mode,count,hash = mo.groups()
                if mode=="trace": continue
                trace = Trace(int(count), int(hash, 16))
                self.table[hash] = trace
            else:
                pc = int(line.strip(), 16)
                trace.frames.append(pc)

    def study(self):
        byChar = []
        for trace in self.table.values():
            byChar.append((trace.character(), trace))
        byChar.sort()
        lastChar = None
        total = 0
        for (character, trace) in byChar:
            if lastChar and lastChar != character:
                print()
            print("%016x %016x %d" % (character&0xffffffffffffffff, trace.hash, trace.count))
            total += trace.count
            lastChar = character
        print("total", total)

Capture().study()
