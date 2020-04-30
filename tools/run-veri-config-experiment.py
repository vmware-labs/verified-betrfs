#!/usr/bin/env python3

from __future__ import print_function
from __future__ import division

import sys
import os

def actuallyprint(msg):
    print(msg)
    sys.stdout.flush()

def autoconfig(config, memlimit):
  actuallyprint("using node size roughly: " + config)
  sys.stdout.flush()

  if memlimit.endswith("gb"):
    memlimit = int(float(memlimit[:-2]) * 1024*1024*1024)
  else:
    memlimit = int(memlimit)

  itable_size = 8*1024*1024

  MALLOC_OVERHEAD=1.00
  if config == "8mb":
    node_size = 8*1024*1024
    bucket_weight = 8356168
    cache_size = int(memlimit // ((8*1024*1024)*MALLOC_OVERHEAD))
  elif config == "1mb":
    node_size = 1*1024*1024
    bucket_weight = 1016136 # jonh has no idea where this number comes from, so I subtracted 32000 because that looks like a popular choice.
    cache_size = int(memlimit // ((1*1024*1024)*MALLOC_OVERHEAD))
  elif config == "64kb":
    node_size = 98304
    bucket_weight = 64220
    cache_size = int(memlimit // ((64*1024)*MALLOC_OVERHEAD))
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
  actuallyprint("starting with default config...")
  ret = os.system("./tools/configure-cgroups.sh")
  assert ret == 0

def set_mem_limit(limit):
  if limit.endswith("gb"):
    val = int(float(limit[:-2]) * 1024*1024*1024)
    actuallyprint("setting mem limit to " + str(val) + " bytes (" + limit + ")")
  else:
    val = int(limit)
    actuallyprint("setting mem limit to " + str(val) + " bytes")

  ret = os.system("echo " + str(val) + " > /sys/fs/cgroup/memory/VeribetrfsExp/memory.limit_in_bytes")
  assert ret == 0

def clear_page_cache():
  if not os.path.exists("tools/clear-os-page-cache"):
    actuallyprint("Error: can't clear cache.")
    actuallyprint("Run `sudo tools/setup-clear-os-page-cache-binary.sh` first.")
    sys.exit(1)

  actuallyprint("Clearing page cache")
  ret = os.system("tools/clear-os-page-cache")
  assert ret == 0

def splice_value_into_bundle(name, value):
  splice_successful = False
  with open("build/Bundle.cpp") as f:
    lineNum = 0
    c = 0
    lines = []
    for line in f:
      lineNum += 1
      if line.strip() == "uint64 __default::" + name + "()":
        c = 1
      else:
        if c == 1:
          c = 2
        elif c == 2:
          line = "    return (uint64)" + value + "; /*hi mom*/\n"
          splice_successful = True
          #actuallyprint("Splicing %s = %s at line %d" % (name, value, lineNum))
          c = 0
      lines.append(line)
    cpp = "".join(lines)
  assert splice_successful

  with open("build/Bundle.cpp","w") as f:
    f.write(cpp)

def main():
  workload = None
  device = None
  mem = None
  value_updates = []
  config = None
  log_stats = False

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
    elif arg == "config-1mb":
      config = "1mb"
    elif arg == "config-8mb":
      config = "8mb"
    elif arg == "rocks":
      rocks = True
    elif arg == "log_stats":
      log_stats = True
    else:
      assert False, "unrecognized argument: " + arg

  if config != None:
    assert not rocks
    assert ram != None
    value_updates = autoconfig(config, ram) + value_updates

  assert workload != None
  assert device != None

  cgroup_defaults()
  if ram != None:
    set_mem_limit(ram)

  ret = os.system("rm -rf build/")
  assert ret == 0

  if not rocks:
    actuallyprint("Building Bundle.cpp...")
    ret = os.system("make build/Bundle.cpp > /dev/null 2> /dev/null")
    assert ret == 0

  for (name, value) in value_updates:
    assert not rocks
    actuallyprint("setting " + name + " to " + value)
    splice_value_into_bundle(name, value)

  if rocks:
    exe = "build/RocksYcsb"
    cmdoption = "--rocks"
  else:
    exe = "build/VeribetrfsYcsb"
    cmdoption = "--veribetrkv"

  make_options = ""
  if log_stats:
    make_options = "LOG_QUERY_STATS=1 "

  actuallyprint("Building executable...")
  sys.stdout.flush()
  cmd = make_options + "make " + exe + " -s -j4 > /dev/null 2> /dev/null"
  actuallyprint(cmd)
  ret = os.system(cmd)
  assert ret == 0

  wl = "ycsb/workload" + workload + "-onefield.spec"
  actuallyprint("workload: " + wl)
  sys.stdout.flush()

  if device == "optane":
    loc = "/scratch0/tjhance/ycsb/"
  elif device == "disk":
    #loc = "/home/tjhance/ycsb/"
    #loc = "/tmp/veribetrfs/"
    loc = "/media/jonh/portable-backup/scratch/"
  else:
    assert False

  actuallyprint("Device type: " + device)
  actuallyprint("Using " + loc)

  ret = os.system("rm -rf " + loc)
  assert ret == 0
  ret = os.system("mkdir " + loc)
  assert ret == 0

  clear_page_cache()

  # bitmask indicating which CPUs we can use
  # See https://linux.die.net/man/1/taskset
  taskset_cmd = "taskset 4 "

  command = taskset_cmd + "cgexec -g memory:VeribetrfsExp ./" + exe + " " + wl + " " + loc + " " + cmdoption
  actuallyprint(command)
  sys.stdout.flush()

  os.system(command)
  assert ret == 0

if __name__ == "__main__":
  main()
