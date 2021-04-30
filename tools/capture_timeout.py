#!/usr/bin/python3

import sys
import time
import subprocess
import shutil
from lib_deps import *

# NB guessing which version operator is running.
scriptdir = os.path.dirname(__file__)
dafny_default = os.path.normpath(os.path.join(scriptdir, "../.dafny/dafny/Binaries/Dafny"))
if not os.path.exists(dafny_default):
    dafny_default = os.path.normpath(os.path.join(scriptdir, "../.dafny/bin/dafny"))

root_fn = sys.argv[1]
deps = depsFromDfySources([root_fn])

capture_tmp = "capture_tmp"
os.mkdir(capture_tmp)
for dep in deps:
    shutil.copyfile(dep.absPath, os.path.join(capture_tmp, os.path.basename(dep.absPath)))

# be nice to extract z3 version, too
subprocess.call([dafny_default, "/version"], stdout=open(os.path.join(capture_tmp, "dafny-version"), "w"))

subprocess.call(["tar", "czf", f"timeout-snapshot-{int(time.time())}.tgz", "-C", capture_tmp, "."])

shutil.rmtree(capture_tmp)

