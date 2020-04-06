#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import re
import sys
import operator
import bisect

class ARow:
    def __init__(self, total_count, open_count, total_byte, open_byte):
        self.total_count = int(total_count)
        self.open_count = int(open_count)
        self.total_byte = int(total_byte)
        self.open_byte = int(open_byte)

field_width = 14+1
arow_width = field_width*4 - 1

def parse_arow(s):
    assert(len(s) == arow_width)
    total_count = s[:field_width]
    open_count = s[field_width:field_width*2]
    total_byte = s[field_width*2:field_width*3]
    open_byte = s[field_width*3:field_width*4]
    return ARow(total_count, open_count, total_byte, open_byte)

def match_arow_line(token, line):
    if not line.startswith(token + " "):
        return None
    arow = parse_arow(line[len(token)+1:len(token)+1+arow_width])
    label = line[len(token)+1+arow_width+1:]
    return (arow, label)

class Experiment:
    def __init__(self, filename):
        self.filename = filename

        self.os_map_total = {}
        self.os_map_heap = {}
    #    allocations = {"small": {} , "large": {}, "total": {}}
        self.microscopes = {}
        self.first_op_completed_t = None
        self.ops_completed = {}
        self.reads_started = {}
        self.reads_completed = {}
        self.writes_started = {}
        self.writes_completed = {}
        self.scopes = {}
        self.kvl_underlying = {}
        self.kvl_underlying_count = {}
        self.accum = {}

        self.parse()
    
    def parse(self):
        print("Parsing %s" % self.filename)
        t = 0
        line_num = 0
        for line in open(self.filename, "r").readlines():
            line_num += 1
            line = line.strip()
            fields = line.split()

            if line.startswith("veribetrkv [op] sync") or line.startswith("rocksdb [op] sync"):
                if self.first_op_completed_t == None:
                    self.first_op_completed_t = t - 2
                self.ops_completed[t] = int(fields[4])
                t += 1

            if line.startswith("os-map-total"):
                self.os_map_total[t] = int(fields[1])
                self.os_map_heap[t] = int(fields[3])

            if line.startswith("iostats "):
                self.reads_started[t] = int(fields[1])
                self.reads_completed[t] = int(fields[3])
                self.writes_started[t] = int(fields[5])
                self.writes_completed[t] = int(fields[7])

            mo = match_arow_line("ma-scope", line)
            if mo:
                arow,label = mo
                if label not in self.scopes:
                    self.scopes[label] = {}
                self.scopes[label][t] = arow

            mo = match_arow_line("ma-microscope", line)
            if mo:
                arow,label = mo
                label = label.split()[-1]   # suffix word. Sorry.
                if label not in self.microscopes:
                    self.microscopes[label] = {}
                self.microscopes[label][t] = arow
            
            if line.startswith("allocationreport stop underyling_count"):
                self.kvl_underlying_count[t] = int(fields[3])
                self.kvl_underlying[t] = int(fields[5])


            mo = re.compile("cache: (\d+) (.*)-(bytes|count)").search(line)
            if mo!=None:
                value,type,unit = mo.groups()
                accum_key = "%s-%s" % (type,unit)
                if accum_key not in self.accum:
                    self.accum[accum_key] = {}
                self.accum[accum_key][t] = int(value)

