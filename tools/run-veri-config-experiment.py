#!/usr/bin/env python3

from __future__ import print_function
from __future__ import division

import sys
import os

def autoconfig(config, memlimit):
  print("using node size roughly: " + config)

  if memlimit.endswith("gb"):
    memlimit = int(float(memlimit[:-2]) * 1024*1024*1024)
  else:
    memlimit = int(memlimit)

  itable_size = 8*1024*1024

  if config == "8mb":
    node_size = 8*1024*1024
    bucket_weight = 8356168
    cache_size = memlimit // (8*1024*1024)
  elif config == "64kb":
    node_size = 98304
    bucket_weight = 64220
    cache_size = memlimit // (64*1024)
  else:
    assert False

  min_index = (itable_size + node_size - 1) // node_size
    
  return [
    ("IndirectionTableBlockSizeUint64", str(itable_size)),
    ("NodeBlockSizeUint64", str(node_size)),
    ("MinNodeBlockIndexUint64", str(min_index)),
    ("MaxTotalBucketWeightUint64", str(bucket_weight)),
    ("MaxCacheSizeUint64", str(cache_size)),
  ]

def cgroup_defaults():
  print("starting with default config...")
  ret = os.system("./tools/configure-cgroups.sh")
  assert ret == 0

def set_mem_limit(limit):
  if limit.endswith("gb"):
    val = int(float(limit[:-2]) * 1024*1024*1024)
    print("setting mem limit to " + str(val) + " bytes (" + limit + ")")
  else:
    val = int(limit)
    print("setting mem limit to " + str(val) + " bytes")

  ret = os.system("echo " + str(val) + " > /sys/fs/cgroup/memory/VeribetrfsExp/memory.limit_in_bytes")
  assert ret == 0

def clear_page_cache():
  if not os.path.exists("tools/clear-os-page-cache"):
    print("Error: can't clear cache.")
    print("Run `sudo tools/setup-clear-os-page-cache-binary.sh` first.")
    sys.exit(1)

  print("Clearing page cache")
  ret = os.system("tools/clear-os-page-cache")
  assert ret == 0

def splice_value_into_bundle(name, value):
  with open("build/Bundle.cpp") as f:
    c = 0
    lines = []
    for line in f:
      if line.strip() == "uint64 __default::" + name + "()":
        c = 1
      else:
        if c == 1:
          c = 2
        elif c == 2:
          line = "    return (uint64)" + value + ";\n"
          c = 0
      lines.append(line)
    cpp = "".join(lines)

  with open("build/Bundle.cpp","w") as f:
    f.write(cpp)

def main():
  workload = None
  device = None
  mem = None
  value_updates = []
  config = None

  rocks = None

  for arg in sys.argv[1:]:
    if arg.startswith("ram="):
      ram = arg[len("ram=") : ]
    elif arg.startswith("workload="):
      workload = arg[len("workload=") : ]
    elif arg.startswith("device="):
      device = arg[len("device=") : ]
    elif "Uint64=" in arg:
      sp = arg.split("=")
      assert len(sp) == 2
      name = sp[0]
      value = sp[1]
      value_updates.append((name, value))
    elif arg == "config-64kb":
      config = "64kb"
    elif arg == "config-8mb":
      config = "8mb"
    elif arg == "rocks":
      rocks = True
    else:
      assert False, "unrecognized argument: " + arg

  assert workload != None
  assert device != None

  if config != None:
    assert not rocks
    assert ram != None
    value_updates = autoconfig(config, ram) + value_updates

  cgroup_defaults()
  if ram != None:
    set_mem_limit(ram)

  ret = os.system("rm -rf build/")
  assert ret == 0

  if not rocks:
    print("Building Bundle.cpp...")
    ret = os.system("make build/Bundle.cpp > /dev/null 2> /dev/null")
    assert ret == 0

  for (name, value) in value_updates:
    assert not rocks
    print("setting " + name + " to " + value)
    splice_value_into_bundle(name, value)

  if rocks:
    exe = "build/RocksYcsb"
    cmdoption = "--rocks"
  else:
    exe = "build/VeribetrfsYcsb"
    cmdoption = "--veribetrkv"

  print("Building executable...")
  ret = os.system("make " + exe + " -s -j4 > /dev/null 2> /dev/null")
  assert ret == 0

  wl = "ycsb/workload" + workload + "-onefield.spec"
  print("workload: " + wl)

  if device == "optane":
    loc = "/scratch0/tjhance/ycsb/"
  elif device == "disk":
    loc = "/home/tjhance/ycsb/"
  else:
    assert False

  print("Device type: " + device)
  print("Using " + loc)

  ret = os.system("rm -rf " + loc)
  assert ret == 0
  ret = os.system("mkdir " + loc)
  assert ret == 0

  clear_page_cache()

  # bitmask indicating which CPUs we can use
  # See https://linux.die.net/man/1/taskset
  taskset_cmd = "taskset 4 "

  command = taskset_cmd + "cgexec -g memory:VeribetrfsExp ./" + exe + " " + wl + " " + loc + " " + cmdoption
  print(command)

  os.system(command)
  assert ret == 0

if __name__ == "__main__":
  main()
