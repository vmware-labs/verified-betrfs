#!/usr/bin/env python3

from __future__ import print_function
from __future__ import division

import sys
import os
import subprocess
import time
import datetime
import signal

def actuallyprint(msg):
    print(msg)
    sys.stdout.flush()

# def splice_value_into_bundle(name, value):
#   splice_successful = False
#   with open("build/Bundle.cpp") as f:
#     lineNum = 0
#     c = 0
#     lines = []
#     for line in f:
#       lineNum += 1
#       if line.strip() == "uint64 __default::" + name + "()":
#         c = 1
#       else:
#         if c == 1:
#           c = 2
#         elif c == 2:
#           line = "    return (uint64)" + value + "; /*hi mom*/\n"
#           splice_successful = True
#           #print("Splicing %s = %s at line %d" % (name, value, lineNum))
#           c = 0
#       lines.append(line)
#     cpp = "".join(lines)
#   assert splice_successful
# 
#   with open("build/Bundle.cpp","w") as f:
#     f.write(cpp)

def main():
  ops=None
  output=None

  print("arguments", sys.argv)

  for arg in sys.argv[1:]:
    if arg.startswith("ops="):
      ram = arg[len("ops=") : ]
    elif arg.startswith("output="):
      output = arg[len("output=") : ]
    else:
      assert False, "unrecognized argument: " + arg

  value_updates = []
  for (name, value) in value_updates:
    print("setting " + name + " to " + value)
    # splice_value_into_bundle(name, value)

  actuallyprint("Building executable...")
  sys.stdout.flush()

  dafny_cmd = ".dafny/dafny/Binaries/dafny /noVerify /spillTargetCode:3 /countVerificationErrors:0 /compileTarget:cpp lib/DataStructures/MutableBtree.i.dfy framework/NativeArrays.h"
  actuallyprint(dafny_cmd)
  ret = os.system(dafny_cmd)
  assert ret == 0

  cmd = "g++ -O3 lib/DataStructures/lib/DataStructures/MutableBtree.i.cpp bench/run-mutable-btree.cpp -o MutableBtreeBench -I .dafny/dafny/Binaries/ -I lib/DataStructures/ -Ilib -std=c++17 -I. -Iframework framework/NativeArrays.cpp"
  actuallyprint(cmd)
  ret = os.system(cmd)
  assert ret == 0

  # bitmask indicating which CPUs we can use
  # See https://linux.die.net/man/1/taskset
  taskset_cmd = "taskset 4 "

  command = taskset_cmd + "./MutableBtreeBench" + " " + ops
  actuallyprint(command)
  sys.stdout.flush()

  proc = subprocess.Popen(command, shell=True, preexec_fn=os.setsid)
  proc_grp_id = os.getpgid(proc.pid)
  actuallyprint("experiment pid %d pgid %d" % (proc.pid, proc_grp_id))

  while proc.poll() == None:
    time.sleep(10)

if __name__ == "__main__":
  main()
