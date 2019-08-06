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

def normPathToRoot(path):
    ### Normalize a path to be relative to ROOT_PATH. Assert if it's outside of ROOT_PATH.
    rootAbsPath = os.path.abspath(ROOT_PATH)
    absPath = os.path.abspath(path)
    assert absPath.startswith(rootAbsPath)
    rootRelPath = absPath[len(rootAbsPath)+1:]
    return rootRelPath

class IncludeReference:
    def __init__(self, origin, line_num, raw_reference):
        self.origin = origin
        self.line_num = line_num
        self.raw_reference = raw_reference
        self.referencing_abs_dir = os.path.abspath(".") if origin is None else origin.dirOf()
        # normalized absolute path to the target of this reference
        self.absPath = os.path.abspath(os.path.join(self.referencing_abs_dir, raw_reference))
        # normalized root-relative path to the target of this reference
        self.normPath = normPathToRoot(self.absPath)

    def validPath(self):
        return True

    def isTrusted(self):
        return self.raw_reference.endswith(".s.dfy")

    def compatiblePath(self):
        return self.isTrusted() or not self.origin.isTrusted()

    def describeOrigin(self):
        if self.origin is None:
            return "cmdline"
        else:
            return self.origin.normPath

    def __repr__(self):
        return "%s (via %s:%d)" % (self.normPath, self.describeOrigin(), self.line_num)

    def __str__(self):
        return repr(self)

    def dirOf(self):
        return os.path.dirname(self.absPath)

    def rootPath(self):
        return self.normPath

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
    def __init__(self, iref, origin):
        self.iref = iref
        self.origin = origin

    def msg(self):
        return "Trusted .s files may only include other trusted .s files; %s includes %s" % (self.origin, self.iref)

    def __str__(self):
        return self.msg()

def visit(iref):
    subIrefs = []
    try:
        contents = open(iref.absPath).readlines()
    except IOError:
        raise IncludeNotFound(iref.absPath, iref.origin)
    for line_num in range(len(contents)):
        line = contents[line_num]
        includePath = fileFromIncludeLine(line)
        if includePath == None:
            continue
        subIref = IncludeReference(iref, line_num+1, includePath)
        if not subIref.validPath():
            raise InvalidDafnyIncludePath(subIref)
        if not subIref.compatiblePath():
            raise IncompatibleIncludeTrustedness(subIref, iref)
        subIrefs.append(subIref)
    return subIrefs

def depsFromDfySource(initialRef):
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

def target(iref, suffix):
    targetRootRelPath = iref.normPath.replace(".dfy", suffix)
    result = "$(BUILD_DIR)/%s" % targetRootRelPath
    return result

def okay(iref):
    return target(iref, ".okay")

def deps(iref):
    return target(iref, ".deps")

def main():
    target = IncludeReference(None, 0, sys.argv[1])
    outputFilename = sys.argv[2]

    output = ""
    output += "# deps from %s\n" % target
    allDeps = depsFromDfySource(target)
    for dep in allDeps:
        output += "%s: %s\n" % (okay(target), okay(dep))
        output += "%s: %s\n\n" % (deps(target), deps(dep))

    outfp = open(outputFilename, "w")
    outfp.write(output)
    outfp.close()

main()
