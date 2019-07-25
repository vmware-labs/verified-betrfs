#!/usr/bin/python

import os
import re
import sys

ROOT_PATH = os.getenv("ROOT")
assert ROOT_PATH

def fileFromIncludeLine(line):
    if not line.startswith("//"):
        mo = re.search('include "(.*)"', line)
        if mo==None:
            return mo
        return mo.groups(1)[0]

class IncludeReference:
    def __init__(self, origin, line_num, raw_reference):
        self.origin = origin
        self.line_num = line_num
        self.raw_reference = raw_reference

    def validPath(self):
        return True

    def __repr__(self):
        return "%s, from %s line %d" % (self.raw_reference, self.origin, self.line_num)

    def __str__(self):
        return repr(self)

    def rootPath(self):
        path = os.path.normpath(
                os.path.join(os.path.dirname(self.origin), self.raw_reference))
        return path

    def __hash__(self):
        return hash(self.rootPath())

    def __cmp__(self, other):
        return cmp(self.rootPath(), other.rootPath())


class IncludeNotFound(Exception):
    def __init__(self, path, referencingPath):
        self.path = path
        self.referencingPath = referencingPath

    def msg(self):
        return "Cannot find file '%s' referenced from '%s'" % (self.path, self.referencingPath)

    def __str__(self):
        return self.msg()

class InvalidDafnyIncludePath(Exception):
    def __init__(self, iref):
        self.iref = iref

    def msg(self):
        return "Includes must not contain ..; got %s" % (self.iref)

    def __str__(self):
        return self.msg()

def visit(iref):
    subIrefs = []
    try:
        contents = open(iref.rootPath()).readlines()
    except IOError:
        raise IncludeNotFound(iref.rootPath(), iref.origin)
    for line_num in range(len(contents)):
        line = contents[line_num]
        includePath = fileFromIncludeLine(line)
        if includePath == None:
            continue
        subIref = IncludeReference(iref.rootPath(), line_num+1, includePath)
        if not subIref.validPath():
            raise InvalidDafnyIncludePath(subIref)
        subIrefs.append(subIref)
    return subIrefs

def depsFromDfySource(path):
    initialRef = IncludeReference("./dummy", 0, path)
    needExplore = [initialRef]
    visited = set()
    while len(needExplore)>0:
        iref = needExplore.pop()
        if iref in visited:
            continue
        visited.add(iref)
        needExplore.extend(visit(iref))
    visited.remove(initialRef)
    return visited

def okay(path):
    path = path.replace(".dfy", ".okay")
    assert path.startswith(ROOT_PATH)
    path = path[len(ROOT_PATH):]
    return "$(BUILD_DIR)/%s" % path

def main():
    target = sys.argv[1]
    outputFilename = sys.argv[2]

    output = ""
    output += "# deps from %s\n" % target
    allDeps = depsFromDfySource(target)
    for dep in allDeps:
        output += "%s: %s\n\n" % (okay(target), okay(dep.rootPath()))

    outfp = open(outputFilename, "w")
    outfp.write(output)
    outfp.close()

main()
