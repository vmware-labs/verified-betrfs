#!/usr/bin/python

import os
import re
import sys
from lib_deps import *

class InvalidDafnyIncludePath(Exception):
    def __init__(self, iref):
        self.iref = iref

    def msg(self):
        return "Includes must not contain ..; got %s" % (self.iref)

    def __str__(self):
        return self.msg()

class UndeclaredTrustedness(Exception):
    def __init__(self, iref):
        self.iref = iref

    def msg(self):
        return "Dafny file %s must declare trustedness with .s.dfy or .i.dfy extension" % self.iref

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
    for dep in allDeps[::-1]:
        output += "%s: %s\n" % (okay(target), okay(dep))
        output += "%s: %s\n\n" % (deps(target), deps(dep))

    outfp = open(outputFilename, "w")
    outfp.write(output)
    outfp.close()

if (__name__=="__main__"):
    main()
