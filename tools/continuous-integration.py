#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT


import os
import shutil
import subprocess
import sys

def callOrDie(*kargs):
    rc = subprocess.call(*kargs)
    if rc!=0:
        raise Exception("%s call failed" % kargs[0])

def main():
    os.chdir("../continuous-integration")

    result = subprocess.Popen(["git", "status"], stdout=subprocess.PIPE).communicate()[0].decode('utf-8')
    if "nothing to commit, working tree clean" not in result:
        raise Exception("Git unclean; git commit hash label would be a lie.")

    githash = subprocess.Popen(["git", "rev-parse", "HEAD"], stdout=subprocess.PIPE).communicate()[0].strip().decode('utf-8')
    
    callOrDie(["make", "-C", "../disk-betree", "status"])

    os.mkdir(githash)
    shutil.copy("../build/disk-betree/Bundle.i.status.pdf", githash)
    callOrDie(["git", "add", githash])
    callOrDie(["git", "commit", "-m", "CI Status Report"])
    callOrDie(["git", "push"])
    
main()
