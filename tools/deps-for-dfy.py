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
        assert origin == None or origin.__class__ == IncludeReference
        self.origin = origin
        self.line_num = line_num
        self.raw_reference = raw_reference
        #print("XXX iref: %s\n\torigin %s\n\traw %s " % (self, self.origin, self.raw_reference))
        #print("XXX\torigin: %s" % self.origin)
        #print("XXX\torigin root: %s" % self.origin.rootPath() if self.origin else None)
        #print("XXX\tdirOf: %s" % self.dirOf())
        #print("XXX\troot: %s" % self.rootPath())

    def validPath(self):
        return True

    def isTrusted(self):
        self.raw_reference.endswith(".s.dfy")

    def compatiblePath(self):
        return self.isTrusted() or not self.origin.isTrusted()

    def __repr__(self):
        return "%s, from %s line %d" % (self.raw_reference, self.origin, self.line_num)

    def __str__(self):
        return repr(self)

    def dirOf(self):
        if self.origin is None:
            return "."
        else:
            result = os.path.dirname(os.path.join(self.origin.dirOf(), self.raw_reference))
            #print ("XXX\t\tdirOf origin dir: %s" % self.origin.dirOf())
            #print ("XXX\t\tdirOf raw: %s" % self.raw_reference)
            #print ("XXX\t\tdirOf result: %s" % result)
            return result

    def rootPath(self):
        path = os.path.normpath(os.path.join(self.dirOf(), self.raw_reference))
        return path

    def __hash__(self):
        return hash(self.rootPath())

    def __cmp__(self, other):
        if other is None:
            return False
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

class IncompatibleIncludeTrustedness(Exception):
    def __init__(self, iref):
        self.iref = iref

    def msg(self):
        return "Trusted .s files may only include other trusted .s files; got %s" % (self.iref)

    def __str__(self):
        return self.msg()

def visit(iref):
    subIrefs = []
    try:
        contents = open(iref.rootPath()).readlines()
    except IOError:
        print ("XXX iref.origin== %s" % iref.origin)
        print ("XXX iref.origin.dirOf() == %s" % iref.origin.dirOf())
        print ("XXX iref.raw_reference == %s" % iref.raw_reference)
        j = os.path.join(iref.dirOf(), iref.raw_reference)
        print ("XXX joined == %s" % j)
        n = os.path.normpath(j)
        print ("XXX norm == %s" % n)
        print ("XXX iref.rootPath() == %s" % iref.rootPath())
        raise IncludeNotFound(iref.rootPath(), iref.origin)
    for line_num in range(len(contents)):
        line = contents[line_num]
        includePath = fileFromIncludeLine(line)
        if includePath == None:
            continue
        subIref = IncludeReference(iref, line_num+1, includePath)
        if not subIref.validPath():
            raise InvalidDafnyIncludePath(subIref)
        if not subIref.compatiblePath():
            raise IncompatibleIncludeTrustedness(subIref)
        subIrefs.append(subIref)
    return subIrefs

def depsFromDfySource(path):
    initialRef = IncludeReference(None, 0, path)
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

def target(dfypath, suffix):
    path = dfypath.replace(".dfy", suffix)
    absPath = os.path.abspath(path)
    absRoot = os.path.abspath(ROOT_PATH)
    assert absPath.startswith(absRoot)
    path = path[len(ROOT_PATH):]
    return "$(BUILD_DIR)/%s" % path

def okay(dfypath):
    return target(dfypath, ".okay")

def deps(dfypath):
    return target(dfypath, ".deps")

def main():
    target = sys.argv[1]
    outputFilename = sys.argv[2]

    output = ""
    output += "# deps from %s\n" % target
    allDeps = depsFromDfySource(target)
    for dep in allDeps:
        output += "%s: %s\n\n" % (okay(target), okay(dep.rootPath()))
        output += "%s: %s\n\n" % (deps(target), deps(dep.rootPath()))

    outfp = open(outputFilename, "w")
    outfp.write(output)
    outfp.close()

main()
