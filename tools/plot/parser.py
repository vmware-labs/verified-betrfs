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

class Trace:
    def __init__(self, label, units):
        self.label = label
        self.units = units
        self.data = {}
        self._sortedKeys = None

    def sortedKeys(self):
        if not self._sortedKeys:
            self._sortedKeys = list(self.data.keys())
            self._sortedKeys.sort()
        return self._sortedKeys

    def __getitem__(self, op):
        if op in self.data:
            return self.data[op]
        else:
            # We interpolate, but not extrapolate
            if op < self.sortedKeys()[0]:
                return None
            if op > self.sortedKeys()[-1]:
                return None
            idx = bisect.bisect(self.sortedKeys(), op)
            if idx == 0:
                return self.data[self.sortedKeys()[0]]
            left_op = self.sortedKeys()[idx - 1]
            right_op = self.sortedKeys()[idx]
            frac = (op - left_op) / float(right_op - left_op)
            left_v = self.data[left_op]
            right_v = self.data[right_op]
            return left_v + frac*(right_v - left_v)

    def __setitem__(self, op, val):
        self.data[op] = val

class Experiment:
    def __init__(self, filename):
        self.filename = filename
        self.nickname = self.filename.split("/")[-1]

        self.elapsed = Trace("elapsed", "s")

        self.operation = Trace("operation", "op")
        self.os_map_total = Trace("os_map_total", "B")
        self.os_map_heap = Trace("os_map_heap", "B")
    #    allocations = {"small": {} , "large": {}, "total": {}}
        self.microscopes = {}
        self.first_op_completed_t = None
        self.ops_completed = Trace("ops_completed", "op")
        # these io counts are an older format that only worked in veribetrfs
        self.reads_started = {}
        self.reads_completed = {}
        self.writes_started = {}
        self.writes_completed = {}
        # these io counts are a newer format that works in rocks too
        self.read_count = Trace("read_count", "iop")
        self.read_bytes = Trace("read_bytes", "B")
        self.write_count = Trace("write_count", "iop")
        self.write_bytes = Trace("write_bytes", "B")

        self.utime = Trace("utime", "s")
        self.stime = Trace("stime", "s")
        self.vsize = Trace("vsize", "B")
        self.rss = Trace("rss", "B")

        self.procio_read_bytes = Trace("procio_read_bytes", "B")
        self.procio_write_bytes = Trace("procio_write_bytes", "B")

        self.jem_allocated = Trace("jem_allocated", "B")
        self.jem_active = Trace("jem_allocated", "B")
        self.jem_mapped = Trace("jem_allocated", "B")

        self.scopes = {}
        self.kvl_underlying = {}
        self.kvl_underlying_count = {}
        self.accum = {}

        self.parse()
        self.sortedOpns = list(self.operation.data.keys())
        self.sortedOpns.sort()
        self.op_max = max(self.sortedOpns)
    
    def parse(self):
        print("Parsing %s" % self.filename)
        cur_op = 0
        cur_t = 0
        line_num = 0

        cur_phase = None
        phase_op_base = 0
        phase_t_base = 0
        self.phase_starts = {}

        for line in open(self.filename, "r").readlines():
            line_num += 1
            line = line.strip()
            fields = line.split()

            # op count is the independent variable for all traces.
            if line.startswith("elapsed"):
                phase = fields[4]
                if phase != cur_phase:
                    cur_phase = phase
                    phase_op_base = cur_op
                    phase_t_base = cur_t
                    self.phase_starts[phase] = phase_op_base
                t_in_phase = int(fields[1])/1000.0
                cur_t = t_in_phase + phase_t_base
                self.elapsed[cur_op] = cur_t
                op_in_phase = int(fields[3])
                cur_op = op_in_phase + phase_op_base
                self.operation[cur_op] = cur_op
                #print(phase, t_in_phase, phase_t_base, t, op_in_phase, cur_op)

#            if line.startswith("veribetrkv [op] sync") or line.startswith("rocksdb [op] sync"):
#                cur_op = int(fields[4])
#                self.operation[cur_op] = cur_op

            if line.startswith("os-map-total"):
                self.os_map_total[cur_op] = int(fields[1])
                self.os_map_heap[cur_op] = int(fields[3])

#            if line.startswith("iostats "):
#                self.reads_started[cur_op] = int(fields[1])
#                self.reads_completed[cur_op] = int(fields[3])
#                self.writes_started[cur_op] = int(fields[5])
#                self.writes_completed[cur_op] = int(fields[7])

            if line.startswith("ioaccounting "):
                self.read_count[cur_op] = int(fields[2])
                self.read_bytes[cur_op] = int(fields[4])
                self.write_count[cur_op] = int(fields[6])
                self.write_bytes[cur_op] = int(fields[8])

            if line.startswith("stat-accounting "):
                self.utime[cur_op] = int(fields[2])
                self.stime[cur_op] = int(fields[4])
                self.vsize[cur_op] = int(fields[6])
                self.rss[cur_op] = int(fields[8])

            if line.startswith("proc-io"):
                self.procio_read_bytes[cur_op] = int(fields[2])
                self.procio_write_bytes[cur_op] = int(fields[4])

#            mo = match_arow_line("ma-scope", line)
#            if mo:
#                arow,label = mo
#                if label not in self.scopes:
#                    self.scopes[label] = {}
#                self.scopes[label][t] = arow
#
#            mo = match_arow_line("ma-microscope", line)
#            if mo:
#                arow,label = mo
#                label = label.split()[-1]   # suffix word. Sorry.
#                if label not in self.microscopes:
#                    self.microscopes[label] = {}
#                self.microscopes[label][t] = arow
#            
#            if line.startswith("allocationreport stop underyling_count"):
#                self.kvl_underlying_count[t] = int(fields[3])
#                self.kvl_underlying[t] = int(fields[5])


            mo = re.compile("Allocated: (\d+), active: (\d+), mapped: (\d+)").search(line)
            if mo!=None:
                (self.jem_allocated[cur_op],
                    self.jem_active[cur_op],
                    self.jem_mapped[cur_op]) = map(int, mo.groups())

            mo = re.compile("cache: (\d+) (.*)-(bytes|count)").search(line)
            if mo!=None:
                value,type,unit = mo.groups()
                accum_key = "%s-%s" % (type,unit)
                if accum_key not in self.accum:
                    self.accum[accum_key] = Trace(accum_key, "unk")
                self.accum[accum_key][cur_op] = int(value)

