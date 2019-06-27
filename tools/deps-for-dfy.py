#!/usr/bin/python

import os
import re
import sys

def fileFromIncludeLine(line):
    mo = re.search('include "(.*)"', line)
    return mo.groups(1)[0]

def visit(path):
    includes = set([fileFromIncludeLine(line) for line in open(path).readlines() if line.startswith("include")])
    paths = [os.path.join(os.path.split(path)[0], include) for include in includes]
    return paths

def depsFromDfySource(path):
    needExplore = [path]
    visited = set()
    while len(needExplore)>0:
        path = needExplore.pop()
        if path in visited: continue
        visited.add(path)
        needExplore.extend(visit(path))
    return visited

print depsFromDfySource(sys.argv[1])
