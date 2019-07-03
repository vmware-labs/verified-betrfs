#!/usr/bin/python

import os
import re
import sys

def fileFromIncludeLine(line):
    mo = re.search('include "(.*)"', line)
    if mo==None:
        return mo
    return mo.groups(1)[0]

class IncludeNotFound(Exception):
    def __init__(self, path, referencingPath):
        self.path = path
        self.referencingPath = referencingPath

    def msg(self):
        return "Cannot find file '%s' referenced from '%s'" % (self.path, self.referencingPath)

    def __str__(self):
        return self.msg()

class InvalidDafnyIncludePath(Exception):
    def __init__(self, path, filename, lineNum):
        self.path = path
        self.filename = filename
        self.lineNum = lineNum

    def msg(self):
        return "Includes must begin with 'inc/'; got %s in %s line %d" % (self.path, self.filename, self.lineNum)

    def __str__(self):
        return self.msg()

def validPath(path):
    return path.startswith("inc/")

def visit(path, referencingPath):
    paths = []
    try:
        contents = open(path).readlines()
    except IOError:
        raise IncludeNotFound(path, referencingPath)
    for lineNum in range(len(contents)):
        line = contents[lineNum]
        includePath = fileFromIncludeLine(line)
        if includePath == None:
            continue
        if not validPath(includePath):
            raise InvalidDafnyIncludePath(includePath, path, lineNum+1)
        paths.append(includePath)
    return paths

def depsFromDfySource(path):
    needExplore = [path]
    visited = set()
    while len(needExplore)>0:
        subPath = needExplore.pop()
        if subPath in visited:
            continue
        visited.add(subPath)
        needExplore.extend(visit(subPath, path))
    return visited

def okay(path):
    path = path.replace(".dfy", ".okay")
    return "$(BUILD_DIR)/%s" % path

def main():
    try:
        target = sys.argv[1]
        outputFilename = sys.argv[2]

        output = ""
        output += "# deps from %s\n" % target
        allDeps = depsFromDfySource(target)
        allDeps.remove(target)
        for dep in allDeps:
            output += "%s: %s\n\n" % (okay(target), okay(dep))

        outfp = open(outputFilename, "w")
        outfp.write(output)
        outfp.close()
    except Exception as ex:
        sys.stderr.write("Kaboom: %s (%s)\n" % (ex, type(ex)))
        sys.exit(-1)
    sys.exit(0)

main()
