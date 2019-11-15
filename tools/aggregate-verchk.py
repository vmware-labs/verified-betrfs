#!/usr/bin/python3

from lib_aggregate import *

def main():
    verchks = [prereq for prereq in sys.argv[1:] if prereq.endswith(".verchk")]
    summaries = [summarize(verchk) for verchk in verchks]
    worstSummary = min(summaries)
    status = 1 if worstSummary isinstance DafnyVerified else 0
    print(status, worstSummary)

main()
