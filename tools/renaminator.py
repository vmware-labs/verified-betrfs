#!/usr/bin/python3
# Automation for moving dfy files among directories, cleaning up include references.

import os
import subprocess

EXCLUDED_DIRS = set([".dafny", "build"])

class Renaminator:
    def __init__(self):
        self.catalog()
        # Apply the include path fixes first, since they're expressed relative
        # to the source path locations.
        self.mkdirCmds = []
        self.fixCmds = []
        self.gitCmds = []

    def catalog(self):
        paths = []
        for root, dirs, files in os.walk("."):
            parts = root.split("/")
            if len(parts) == 1:
                # must be "."
                top = parts[0]
            else:
                top = parts[1]
            if top in EXCLUDED_DIRS or (top[0]=='.' and len(top)>1):
                continue
            for file in files:
                if not file.endswith(".dfy"):
                    continue
                fullpath = os.path.join(root, file)
                paths.append(fullpath)
        self.paths = paths

    def findSourceDir(self, filename):
        matchingSourcePaths = [path for path in self.paths if path.endswith("/"+filename)]
        if len(matchingSourcePaths) == 0:
            raise Exception("No path matches %s" % filename)
        if len(matchingSourcePaths) > 1:
            raise Exception("Multiple paths match %s: %s" % (filename, matchingSourcePaths))
        path = matchingSourcePaths[0]
        return path[:-(len(filename)+1)]

    def containsLine(self, filepath, testString):
        contents = open(filepath).read()
        return testString in contents

    def fixReferrer(self, referrer, targetFilename, sourceDir, destDir):
        referrerPath = os.path.split(referrer)[0]
        sourceRelative = os.path.relpath(os.path.join(sourceDir, targetFilename), referrerPath)
        destRelative = os.path.relpath(os.path.join(destDir, targetFilename), referrerPath)
        expectInclude = 'include "%s"' % sourceRelative
        newInclude = 'include "%s"' % destRelative
        if self.containsLine(referrer, expectInclude):
            self.fixCmds.append(["sed", "-i", "/include/s#%s#%s#" % (expectInclude, newInclude), referrer])

    def relocate(self, filename, destDir):
        self.mkdirCmds.append(["mkdir", destDir])
        sourceDir = self.findSourceDir(filename)
        sourceName = os.path.join(sourceDir, filename)
        destName = os.path.join(destDir, filename)
        self.gitCmds.append(["git", "mv", sourceName, destName])
        self.gitCmds.append(["git", "add", destName])

        for referrer in self.paths:
            self.fixReferrer(referrer, filename, sourceDir, destDir)

    def enact(self):
        for cmd in self.fixCmds + self.mkdirCmds + self.gitCmds:
            print(cmd)
            subprocess.call(cmd)

renaminator = Renaminator()
def moveinto(destDir, filenamesStr):
    for filename in filenamesStr.strip().split():
        renaminator.relocate(filename, destDir)


moveinto("MapSpec", """
AsyncDiskModel.s.dfy
MapSpec.s.dfy
ThreeStateVersionedMap.s.dfy
ThreeStateVersioned.s.dfy
UI.s.dfy
UIStateMachine.s.dfy
""")

moveinto("Betree", """
Betree.i.dfy
BetreeInv.i.dfy
Betree_Refines_Map.i.dfy
BetreeSpec.i.dfy
Transactable.i.dfy
Graph.i.dfy
BlockInterface.i.dfy
""")

moveinto("PivotBetree", """
PivotBetree.i.dfy
PivotBetree_Refines_Betree.i.dfy
PivotBetree_Refines_Map.i.dfy
PivotBetreeSpec.i.dfy
PivotBetreeSpecRefinement.i.dfy
PivotsLib.i.dfy
Bounds.i.dfy
BucketsLib.i.dfy
BucketWeights.i.dfy
""")

# Introduces the Block Cache, shows that it's 3-state crash safe, and
# then staples it onto a Betree to get a crash-safe pivot tree.
moveinto("BlockCacheSystem", """
AsyncSectorDiskModel.i.dfy
BlockCache.i.dfy
BlockCacheSystem.i.dfy
BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface.i.dfy
BetreeBlockCache.i.dfy
BetreeBlockCacheSystem.i.dfy
BetreeBlockCacheSystem_Refines_ThreeStateVersionedPivotBetree.i.dfy
ThreeStateVersionedPivotBetree.i.dfy
""")

moveinto("Impl", """
KVList.i.dfy
KVListPartialFlush.i.dfy
""")

renaminator.enact()
