#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT


import json
from lib_aggregate import *

def main(reportType, inputs):
    verchks = [prereq for prereq in inputs if prereq.endswith("."+reportType)]
    summaries = sorted([summarize(reportType, verchk) for verchk in verchks])
    worstSummary = min(summaries)
    result = {
        'is_success': worstSummary.is_success,
        'worst': worstSummary.json(),
        'summaries': [summary.json() for summary in summaries]
    }
    print(json.dumps(result, sort_keys=True, indent=4))

reportType = sys.argv[1]
inputs = sys.argv[2:]
if (not reportType in [SYNCHK, VERCHK]):
    raise Exception("usage: %0 <%s|%s>" % (sys.argv[0], VERCHK, SYNCHK))
main(reportType, inputs)
