#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


import json
from lib_aggregate import *
from lib_deps import *

def main(reportType, input):
    deps = depsFromDfySources([dafnyFromVerchk(input)])
    verchks = [verchkFromDafny(dep.normPath, reportType) for dep in deps]
    summaries = sorted([summarize(reportType, verchk) for verchk in verchks])
    worstSummary = min(summaries)
    result = {
        'is_success': worstSummary.is_success,
        'worst': worstSummary.json(),
        'summaries': [summary.json() for summary in summaries]
    }
    print(json.dumps(result, sort_keys=True, indent=4))

assert(len(sys.argv)==3)
reportType = sys.argv[1]
input = sys.argv[2]
if (not reportType in [SYNCHK, VERCHK]):
    raise Exception("usage: %0 <%s|%s>" % (sys.argv[0], VERCHK, SYNCHK))
main(reportType, input)
