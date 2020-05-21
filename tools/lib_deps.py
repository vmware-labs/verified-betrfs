import os
import sys
import re

try:
    import toposort
except ModuleNotFoundError:
    sys.stderr.write("*****************************************\n")
    sys.stderr.write("** Python3 needs toposort module. Try: **\n")
    sys.stderr.write("** pip3 install toposort               **\n")
    sys.stderr.write("*****************************************\n")
    sys.exit(-1)

# find veribetrfs root relative to this file's location in /tools/
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
ROOT_PATH = os.path.abspath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

# If makefile specified a root, assert it matches.
ROOT_FROM_MAKE = os.getenv("ROOT")
if ROOT_FROM_MAKE != None:
    ROOT_FROM_MAKE = os.path.abspath(ROOT_FROM_MAKE)
    #print "ROOT_FROM_MAKE ==", ROOT_FROM_MAKE
    #print "ROOT_PATH ==", ROOT_PATH
    assert ROOT_FROM_MAKE == ROOT_PATH

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

    def declaresTrustedness(self):
        return self.raw_reference.endswith(".s.dfy") or self.raw_reference.endswith(".i.dfy")

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

    def _tuple(self):
        return (self.absPath,)

    def __hash__(self):
        return hash(self._tuple())

    # Python3
    def __lt__(self, other):
        return self._tuple() < other._tuple()

    def __eq__(self, other):
        return self._tuple() == other._tuple()

    # Python2
    def __cmp__(self, other):
        if other is None:
            return False
        return cmp(self._tuple(), other._tuple())


class IncludeNotFound(Exception):
    def __init__(self, path, referencingPath):
        self.path = path
        self.referencingPath = referencingPath

    def msg(self):
        return "Cannot find file '%s' referenced from '%s'" % (self.path, self.referencingPath)

    def __str__(self):
        return self.msg()

def fileFromIncludeLine(line):
    if not line.startswith("//"):
        mo = re.search('^include "(.*)"', line)
        if mo==None:
            return mo
        return mo.groups(1)[0]

def includePaths(iref):
    try:
        contents = open(iref.absPath).readlines()
    except IOError:
        raise IncludeNotFound(iref.absPath, iref.origin)
    irefs = []
    for line_num in range(len(contents)):
        line = contents[line_num]
        includePath = fileFromIncludeLine(line)
        if includePath == None:
            continue
        subIref = IncludeReference(iref, line_num+1, includePath)
        irefs.append(subIref)
    return irefs

def childrenForIref(iref):
    subIrefs = []
    for subIref in includePaths(iref):
        if not subIref.validPath():
            raise InvalidDafnyIncludePath(subIref)
        if not subIref.declaresTrustedness():
            raise UndeclaredTrustedness(subIref)
        if not subIref.compatiblePath():
            raise IncompatibleIncludeTrustedness(subIref, iref)
        subIrefs.append(subIref)
    return subIrefs

def depsFromDfySource(initialRef):
    needExplore = [initialRef]
    visited = []
    while len(needExplore)>0:
        iref = needExplore.pop()
        if iref in visited:
            continue
        visited.append(iref)
        needExplore.extend(childrenForIref(iref))
    visited.remove(initialRef)
    return visited

def depsFromDfySources(roots):
    """roots are file pathnames"""
    irefs = set()
    for i in range(len(roots)):
        dafnyRoot = roots[i]
        rootIref = IncludeReference(None, i, dafnyRoot)
        irefs.add(rootIref)
        targets = depsFromDfySource(rootIref)
        irefs = irefs.union(set(targets))
    return irefs

def targetName(iref, suffix):
    targetRootRelPath = iref.normPath.replace(".dfy", suffix)
    result = "build/%s" % targetRootRelPath
    return result

def toposortGroup(candidateIrefs):
    """Given a set of IRefs, returns a list of irefs toposorted based on the include graph."""
    graph = {}
    for iRef in candidateIrefs:
        graph[iRef] = set(includePaths(iRef))
    candidateSet = set(candidateIrefs)
    output = []
    for group in toposort.toposort(graph):
        group = list(group.intersection(candidateSet))
        group.sort()
        output += group
    return output
