#!/usr/bin/python3

import os
import subprocess

os.chdir("../continuous-integration")
result = subprocess.Popen(["git", "status"], stdout=subprocess.PIPE).communicate()
print(result)
#subprocess.call(["make", "-C", "../disk-betree", "status"])
