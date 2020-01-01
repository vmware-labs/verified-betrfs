#!/usr/bin/env python3
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
        self.gitAddCmds = []    # some of these will be pre-move referrers, so do them first
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

    def fixReferrer(self, referrer, sourceDir, sourceFilename, destDir, destFilename):
        referrerPath = os.path.split(referrer)[0]
        sourceRelative = os.path.relpath(os.path.join(sourceDir, sourceFilename), referrerPath)
        destRelative = os.path.relpath(os.path.join(destDir, destFilename), referrerPath)
        expectInclude = 'include "%s"' % sourceRelative
        newInclude = 'include "%s"' % destRelative
        if self.containsLine(referrer, expectInclude):
            self.fixCmds.append(["sed", "-i", "/include/s#%s#%s#" % (expectInclude, newInclude), referrer])
            self.gitAddCmds.append(["git", "add", referrer])

    def relocate(self, filename, destDir):
        self.mkdirCmds.append(["mkdir", destDir])
        sourceDir = self.findSourceDir(filename)
        sourceName = os.path.join(sourceDir, filename)
        destName = os.path.join(destDir, filename)
        self.gitCmds.append(["git", "mv", sourceName, destName])

        for referrer in self.paths:
            self.fixReferrer(referrer, sourceDir, filename, destDir, filename)

    def renameInPlace(self, sourceName, destName):
        sourceDir = self.findSourceDir(sourceName)
        sourcePath = os.path.join(sourceDir, sourceName)
        destPath = os.path.join(sourceDir, destName)
        self.gitCmds.append(["git", "mv", sourcePath, destPath])

        for referrer in self.paths:
            self.fixReferrer(referrer, sourceDir, sourceName, sourceDir, destName)
        # print a suggested module renaming command
        print("sed -i 's/\<%s\>/%s/g' *.dfy" % (sourceName.replace(".i.dfy", ""), destName.replace(".i.dfy", "")))

    def enact(self):
        for cmd in self.fixCmds + self.mkdirCmds + self.gitAddCmds + self.gitCmds:
            print(cmd)
            subprocess.call(cmd)

renaminator = Renaminator()
def moveinto(destDir, filenamesStr):
    for filename in filenamesStr.strip().split():
        renaminator.relocate(filename, destDir)

def rename(sourceName, destName):
    renaminator.renameInPlace(sourceName, destName)

#moveinto("BlockCacheSystem", """
#AsyncDiskModel.s.dfy
#""")

rename("Handlers.i.dfy", "MainHandlers.i.dfy")

renaminator.enact()
