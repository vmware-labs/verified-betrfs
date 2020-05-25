#!/usr/bin/env python3

import sys

class ParsedQILog:
    def __init__(self, logfilename):
        self.map = {}
        for line in open(logfilename).readlines():
            fields = line.split()
            if len(fields) < 6 or fields[0] != "Prover":
                continue
            loc = fields[3]
            count = int(fields[5])
            if loc not in self.map:
                self.map[loc] = 0
            if count > self.map[loc]:
                self.map[loc] = count

    def display(self):
        pairs = [(count, loc) for loc,count in self.map.items()]
        pairs.sort()
        for count, loc in pairs:
            print("%8d %-1s" % (count, loc))

class CompareRecord:
    def __init__(self, loc, small_value, big_value):
        self.loc = loc
        self.small_value = small_value
        self.big_value = big_value
        self.ratio = big_value / float(small_value) if small_value != 0 else 99

    def __repr__(self):
        return ("%6.1f %8d %8d %-1s" % (self.ratio, self.small_value, self.big_value, self.loc))

class Comparison:
    def __init__(self, small_filename, big_filename):
        self.small_parsed = ParsedQILog(small_filename)
        self.big_parsed = ParsedQILog(big_filename)

        self.recs = []
        locs = set(self.small_parsed.map.keys()).union(set(self.big_parsed.map.keys()))
        for loc in locs:
            small_value = self.small_parsed.map.get(loc, 1)
            big_value = self.big_parsed.map.get(loc, 1)
            self.recs.append(CompareRecord(loc, small_value, big_value))

    def display(self):
        recs = self.recs
        recs.sort(key = lambda rec: rec.big_value)
        #recs.sort(key = lambda rec: rec.ratio)
        for rec in recs:
            print(rec)

def main():
    args = sys.argv[1:]
    if len(args) == 1:
        ParsedQILog(*args).display()
    elif len(args) == 2:
        Comparison(*args).display()
    else:
        sys.stderr.write("Usage: %s <qi.log> [qi2.log]\n")
        sys.stderr.write("With two arguments: sorts references by ratio of counts in second file. Use with different timeouts to see which qis grow most.\n")

main()
