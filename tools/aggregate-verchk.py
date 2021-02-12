#!/usr/bin/env python3

from lib_aggregate import *

def main(reportType, inputs):
    verchks = [prereq for prereq in inputs if prereq.endswith("."+reportType)]
    print(verchks)
    summaries = [summarize(reportType, verchk) for verchk in verchks]
    worstSummary = min(summaries)
    status = 1 if isinstance(worstSummary, DafnyVerified) else 0
    print(status, worstSummary, worstSummary.verchk)

reportType = sys.argv[1]
inputs = sys.argv[2:]
if (not reportType in [SYNCHK, VERCHK]):
    raise Exception("usage: %0 <%s|%s>" % (sys.argv[0], VERCHK, SYNCHK))
main(reportType, inputs)
