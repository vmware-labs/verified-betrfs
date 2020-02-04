#!/usr/bin/env python3
"""
line_counter.py: attribute lines of veribetrfs source as {spec,code,proof}.
Emulates counting policy from IronFleet to facilitate comparison.
https://github.com/microsoft/Ironclad/blob/master/ironfleet/tools/scripts/dafny-line-count.py

Plan:
Processing individual files is slow, so we'll use make to preserve results.
.s.dfy -> spec
{Impl/*Impl.i.dfy} -> proof, impl
all others -> proof

Then an aggregator extracts numbers from those line-count files.
"""

import sys
import line_count_lib
import line_counter_report_lib
import lib_aggregate
import argparse
import json

parser = argparse.ArgumentParser(description="Count lines of Iron* code and categorize.")
parser.add_argument("--mode", dest="mode", help="count: count one file. report: gather a report for this file and its dependencies", required=True, choices=["count", "report"])
parser.add_argument("--input", dest="input", help=".dfy file to process", required=True)
parser.add_argument("--output", dest="output", help="build file to write result", required=True)

def loadFile(synchk):
    return line_count_lib.DafnyFile(
            lib_aggregate.dafnyFromVerchk(synchk),
            lib_aggregate.summarize(lib_aggregate.SYNCHK, synchk).userTimeSec)

# Ironfleet overcounted impl, because anything in the system that wasn't
# ghost or .s.dfy was counted as impl. That would include refinement models.
# I don't think Ironfleet was careful to ensure that all refinement models
# were ghost-y. Plus this counts "import" statements and other boilerplate
# in the refinement modules as impl.
# I'm not yet sure what rule we should use in veribetrfs. I think there's some
# real non-ghost code in random libraries and the occasional "function method"
# that's both abstract and implementation. But we sure shouldn't be
# billing Model code to impl; it's proof! Will look at the output.

def count(input, output):
    counter = line_count_lib.Counter(".")
    dafnyFile = line_count_lib.DafnyFile(input, 0.0)
    counter.collect_line_counts([dafnyFile])
    obj = {"spec":dafnyFile.spec, "impl":dafnyFile.impl, "proof":dafnyFile.proof}
    fp = open(output, "w")
    json.dump(obj, fp)
    fp.write("\n")
    fp.close()

def main():
    args = parser.parse_args()
    if args.mode == "count":
        count(args.input, args.output)
    elif args.mode == "report":
        line_counter_report_lib.report(args.input, args.output)
    else:
        raise Exception("argparse allowed bogus mode")

main()
