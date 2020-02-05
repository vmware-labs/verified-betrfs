#!/usr/bin/python3
import sys
import subprocess

def get_dafny_hash():
    (value,_) = subprocess.Popen(["git", "rev-parse", "HEAD", ".dafny"], stdout=subprocess.PIPE).communicate()
    return value.decode("utf-8").split("\n")[0]

def parse_args(KNOWN_KEYS, usage):
    """Parse args from command line into buckets of arrays.
    KNOWN_KEYS is  list of argument names."""
    key = None
    buckets = {}
    for arg in sys.argv[1:]:
        if arg.startswith("--"):
            key = arg[2:]
            if key not in KNOWN_KEYS:
                usage("Unknown arg '%s'" % arg)
        elif key==None:
            usage("Unknown arg '%s'" % arg)
        else:
            if key not in buckets:
                buckets[key] = []
            buckets[key].append(arg)
    return buckets

