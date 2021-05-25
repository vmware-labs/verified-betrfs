#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


import json
from lib_aggregate import *
from lib_deps import *
import argparse

def write_summary(reportType, verchks, summary_filename, error_filename):
    #assert(reportType == VERCHK)    # TODO: Do we need syntax summary files?

    # Phase 1: Collect all the failures and write out error details
    fails = {}
    failTypes = {}
    total_time = 0
    timed_conditions = []
    with open(error_filename, 'w') as err:
        for verchk in verchks:
            content, condition = summarize_verbose(reportType, verchk)
            if not condition.userTimeSec is None:
                total_time += condition.userTimeSec
                timed_conditions.append(condition)

            if not condition.is_success:
                # Write the details to the error log
                err.write(dafnyFromVerchk(verchk))
                err.write("\n")
                for line in content.splitlines():
                    err.write("\t%s\n" % line)
                err.write("\n")

                # Categorize the failure
                if condition.level not in fails:
                    fails[condition.level] = []
                    failTypes[condition.level] = condition.result
                fails[condition.level].append(dafnyFromVerchk(verchk))

    with open(summary_filename, 'w') as summary:
        if len(fails) == 0:
            summary.write("Overall: Success\n")
        else:
            summary.write("Overall: Fail\n")

        for level in sorted(fails.keys()):
            summary.write("\nFiles failing with %s\n" % failTypes[level])
            for fail in sorted(fails[level]):
                summary.write("\t%s\n" % fail)

        summary.write("\nTotal build time: %d seconds\n" % int(total_time))
        summary.write("\nSlowest files:\n") 
        for condition in sorted(timed_conditions, reverse=True, key=lambda c : c.userTimeSec)[:10]:
            summary.write("\t%s\t%s\n" % (condition.userTimeSec, condition.filename))


def create_report(reportType, verchks):
    summaries = sorted([summarize(reportType, verchk) for verchk in verchks])
    worstSummary = min(summaries)
    result = {
        'is_success': worstSummary.is_success,
        'worst': worstSummary.json(),
        'summaries': [summary.json() for summary in summaries]
    }
    print(json.dumps(result, sort_keys=True, indent=4))

def main():
    parser = argparse.ArgumentParser(description=\
            'Aggregate syntax/verification results for the supplied file and its dependencies')
    
    type_group = parser.add_mutually_exclusive_group(required=True)
    type_group.add_argument('--verchk', action='store_const', const=VERCHK, default=None,
                            help='Full verification check')
    type_group.add_argument('--synchk', action='store_const', const=SYNCHK, default=None,
                            help='Basic syntax check')
    parser.add_argument('--root', action='store', required=True, help='Base file to start with')

    parser.add_argument('--summary', action='store', required=True, help='Summary of results')
    parser.add_argument('--errors', action='store', required=True, help='Detailed error report')

    args = parser.parse_args()

    reportType = args.verchk if not args.verchk is None else args.synchk
    
    deps = depsFromDfySources([dafnyFromVerchk(args.root)])
    verchks = [verchkFromDafny(dep.normPath, reportType) for dep in deps]
    
    # Old report style
    # create_report(reportType, verchks)

    write_summary(reportType, verchks, args.summary, args.errors)




if (__name__=="__main__"):
  main()

