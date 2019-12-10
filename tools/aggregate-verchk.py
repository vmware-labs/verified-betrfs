#!/usr/bin/env python3

from lib_aggregate import *

def main():
    verchks = [prereq for prereq in sys.argv[1:] if prereq.endswith(".verchk")]
    print(verchks)
    summaries = [summarize("verchk", verchk) for verchk in verchks]
    worstSummary = min(summaries)
    status = 1 if isinstance(worstSummary, DafnyVerified) else 0
    print(status, worstSummary, worstSummary.verchk)

main()
