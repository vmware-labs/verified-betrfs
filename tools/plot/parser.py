#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import re
import sys
import operator
import bisect

field_width = 14+1
arow_width = field_width*4 - 1

class BaseTrace:
    """Time-series data set addressed by opn."""
    def __init__(self, label, units):
        self.label = label
        self.units = units
        self.data = {}
        self._sortedKeys = None
    
    def empty(self):
        return len(self.data) == 0

    def sortedKeys(self):
        if not self._sortedKeys:
            self._sortedKeys = list(self.data.keys())
            self._sortedKeys.sort()
        return self._sortedKeys

    def idxAfter(self, op):
        # Never extrapolate
        if len(self.sortedKeys())==0:
            return None
        if op < self.sortedKeys()[0]:
            return None
        if op > self.sortedKeys()[-1]:
            return None
        return bisect.bisect(self.sortedKeys(), op)

    def __setitem__(self, op, val):
        self.data[op] = val

class Trace(BaseTrace):
    """Interpolated values addressed by opn."""
    def __init__(self, label, units):
        super().__init__(label, units)

    def __getitem__(self, op):
        if op in self.data:
            return self.data[op]
        else:
            idx = self.idxAfter(op)
            if idx==None: return None
            if idx == 0:
                return self.data[self.sortedKeys()[0]]
            left_op = self.sortedKeys()[idx - 1]
            right_op = self.sortedKeys()[idx]
            frac = (op - left_op) / float(right_op - left_op)
            left_v = self.data[left_op]
            right_v = self.data[right_op]
            return left_v + frac*(right_v - left_v)

class DiscreteTrace(BaseTrace):
    """Un-interpolatable values addressed by opn."""
    def __init__(self, label, units):
        super().__init__(label, units)

    def __getitem__(self, op):
        if op in self.data:
            return self.data[op]
        else:
            idx = self.idxAfter(op)
            if idx == None: return None
            return self.data[self.sortedKeys()[idx]]

class ARow:
    def __init__(self, total_count, open_count, total_byte, open_byte):
        self.field = {}
        self.field["total_count"] = int(total_count)
        self.field["open_count"] = int(open_count)
        self.field["total_byte"] = int(total_byte)
        self.field["open_byte"] = int(open_byte)

class ARows:
    def __init__(self, label):
        self.label = label
        self.arows = {}

    def __setitem__(self, op, val):
        self.arows[op] = val

    def getTrace(self, field):
        unit = "B" if field.endswith("_byte") else "cnt"
        trace = Trace(self.label + "." + field, unit)
        for op,arow in self.arows.items():
            trace[op] = arow.field[field]
        return trace

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

class CDF:
    def __init__(self, fields):
        self.xs = [float(f.split(":")[0]) for f in fields]
        self.ys = [float(f.split(":")[1]) for f in fields]

class Experiment:
    def __init__(self, filename, nickname=None):
        self.filename = filename
        if nickname:
            self.nickname = nickname
        else:
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
        self.cgroups_memory_usage_bytes = Trace("cgroups_memory_usage_bytes", "B")

        self.jem_allocated = Trace("jem_allocated", "B")
        self.jem_active = Trace("jem_allocated", "B")
        self.jem_mapped = Trace("jem_allocated", "B")

        self.cgroups_stat = {}

        self.scopes = {}
        self.kvl_underlying = Trace("underlying_bytes", "B")
        self.kvl_underlying_count = Trace("underlying_cnt", "cnt")
        self.accum = {}

        self.rocks_io_reads = Trace("rocksio_reads", "page")
        self.rocks_io_hits = Trace("rocksio_hits", "page")
        self.rocks_io_writes = Trace("rocksio_writes", "page")

        self.iolatency_read = DiscreteTrace("read-latency", "cycles")
        self.iolatency_write = DiscreteTrace("write-latency", "cycles")

        self.slow_thresh = Trace("slow_thresh", "cycles")
        self.slow_reads = Trace("slow_reads", "count")
        self.slow_writes = Trace("slow_writes", "count")

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
                # some bug in heap accounting causes this number to go wacky.
                # Not sure why it doesn't affect the total!
                heap = int(fields[3])
                if heap > 0 and heap < (300<<30):
                    self.os_map_heap[cur_op] = heap

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

            if line.startswith("cgroups-memory.usage_in_bytes"):
                self.cgroups_memory_usage_bytes[cur_op] = int(fields[1])

#            mo = match_arow_line("ma-scope", line)
#            if mo:
#                arow,label = mo
#                if label not in self.scopes:
#                    self.scopes[label] = {}
#                self.scopes[label][t] = arow

            mo = match_arow_line("ma-microscope", line)
            if mo:
                arow,label = mo
                label = label.split()[-1]   # suffix word. Sorry.
                if label not in self.microscopes:
                    self.microscopes[label] = ARows(label)
                self.microscopes[label][cur_op] = arow

            if line.startswith("allocationreport stop underyling_count"):
                self.kvl_underlying_count[cur_op] = int(fields[3])
                self.kvl_underlying[cur_op] = int(fields[5])


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

            if line.startswith("rocks_io_model"):
                self.rocks_io_reads[cur_op] = int(fields[6])
                self.rocks_io_hits[cur_op] = int(fields[8])
                if len(fields)>=10:
                    self.rocks_io_writes[cur_op] = int(fields[10])

            if line.startswith("cgroups-memory.stat"):
                statName = fields[1]
                if statName not in self.cgroups_stat:
                    self.cgroups_stat[statName] = Trace("cgroups-stat-"+statName, "cnt")
                self.cgroups_stat[statName][cur_op] = int(fields[2])

            if line.startswith("io-latency"):
                ptr = {"read":self.iolatency_read, "write":self.iolatency_write}[fields[1]]
                ptr[cur_op] = CDF(fields[2:])

            if line.startswith("ioaccounting-slow"):
                self.slow_thresh[cur_op] = int(fields[2])
                self.slow_reads[cur_op] = int(fields[4])
                self.slow_writes[cur_op] = int(fields[6])
