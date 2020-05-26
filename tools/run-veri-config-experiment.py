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

def autoconfig(config, memlimit, nodeCountFudge):
  actuallyprint("using node size roughly: " + config)
  sys.stdout.flush()

  if memlimit.endswith("gb"):
    memlimit = int(float(memlimit[:-2]) * 1024*1024*1024)
  else:
    memlimit = int(memlimit)

  itable_size = 8*1024*1024

  if config == "8mb":
    node_size = 8*1024*1024
    bucket_weight = 8356168
    cache_size = int(memlimit * nodeCountFudge // ((8*1024*1024)))
  elif config == "1mb":
    node_size = 1*1024*1024
    bucket_weight = 1016136 # jonh has no idea where this number comes from, so I subtracted 32000 because that looks like a popular choice.
    cache_size = int(memlimit * nodeCountFudge // ((1*1024*1024)))
  elif config == "64kb":
    node_size = 98304
    bucket_weight = 64220
    cache_size = int(memlimit * nodeCountFudge // ((64*1024)))
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

  val = int(val)
  ret = os.system("echo " + str(val) + " > /sys/fs/cgroup/memory/VeribetrfsExp/memory.limit_in_bytes")
  assert ret == 0

def clear_page_cache():
  os.system("sudo tools/setup-clear-os-page-cache-binary.sh")

  if not os.path.exists("tools/clear-os-page-cache"):
    print("Error: can't clear cache.")
    print("Run `sudo tools/setup-clear-os-page-cache-binary.sh` first.")
    sys.exit(1)

  print("Clearing page cache")
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
          #print("Splicing %s = %s at line %d" % (name, value, lineNum))
          c = 0
      lines.append(line)
    cpp = "".join(lines)
  assert splice_successful

  with open("build/Bundle.cpp","w") as f:
    f.write(cpp)

def main():
  archive_dir = "/mnt/xvde/archives"
  workload = None
  device = None
  mem = None
  value_updates = []
  config = None
  log_stats = False
  nodeCountFudge = 1.0  # Pretend we have more memory when computing node count budget, since mean node is 75% utilized. This lets us tune veri to exploit all available cgroup memory.
  max_children = None   # Default
  cgroup_enabled = True
  use_unverified_row_cache = None
  use_filters = None
  from_archive = None
  
  veri = None
  rocks = None
  berkeley = None
  kyoto = None
  time_budget_sec = 3600*24*365 # You get a year if you don't ask for a budget

  fp = None

  for arg in sys.argv[1:]:
    if arg.startswith("ram="):
      ram = arg[len("ram=") : ]
    elif arg.startswith("workload="):
      workload = arg[len("workload=") : ]
    elif arg.startswith("device="):
      device = arg[len("device=") : ]
    elif arg.startswith("fromArchive="):
        from_archive = arg[len("fromArchive=") : ]
    elif arg.startswith("nodeCountFudge="):
      nodeCountFudge = float(arg[len("nodeCountFudge=") : ])
    elif "Uint64=" in arg:
      sp = arg.split("=")
      assert len(sp) == 2
      name = sp[0]
      value = sp[1]
      value_updates.append((name, value))
    elif arg == "use_unverified_row_cache":
        use_unverified_row_cache = True
    elif arg == "use_filters":
        use_filters = True
    elif arg == "config-64kb":
      config = "64kb"
    elif arg == "config-8mb":
      config = "8mb"
    elif arg == "veri":
      veri = True
    elif arg == "rocks":
      rocks = True
    elif arg == "berkeley":
      berkeley = True
    elif arg == "kyoto":
      kyoto = True
    elif arg == "log_stats":
      log_stats = True
    elif arg.startswith("time_budget="):
      val_str = arg.split("=")[1]
      unit = val_str[-1]
      mult = 1 if unit=="s" else 60 if unit=="m" else 3600 if unit=="h" else None
      assert mult, "time_budget needs a unit"
      time_budget_sec = float(val_str[:-1]) * mult
    elif arg.startswith("cgroup="):
      enabled = arg.split("=")[1]
      cgroup_enabled = enabled=="True"
    elif arg.startswith("output="):
      outpath = arg.split("=")[1]
      actuallyprint("outpath: %s" % outpath)
      assert not os.path.exists(outpath)
      fp = open(outpath, "w")
    else:
      assert False, "unrecognized argument: " + arg

  assert fp is not None
      
  actuallyprint("Experiment time budget %s" % (datetime.timedelta(seconds=time_budget_sec)))
  actuallyprint("metadata time_budget %s seconds" % time_budget_sec)

  assert veri or rocks or berkeley or kyoto

  if use_unverified_row_cache:
      assert veri

  if use_filters:
      assert rocks
      
  if config != None:
    assert veri
    assert ram != None
    value_updates = autoconfig(config, ram, nodeCountFudge) + value_updates

  assert workload != None
  assert device != None

  cgroup_defaults()
  if ram != None:
    set_mem_limit(ram)

  ret = os.system("rm -rf build/")
  assert ret == 0

  if veri:
    print("Building Bundle.cpp...")
    ret = os.system("make build/Bundle.cpp > /dev/null 2> /dev/null")
    assert ret == 0

  for (name, value) in value_updates:
    assert veri
    print("setting " + name + " to " + value)
    splice_value_into_bundle(name, value)

  if rocks:
    exe = "build/RocksYcsb"
  elif berkeley:
      exe = "build/BerkeleyYcsb"
  elif kyoto:
      exe = "build/KyotoYcsb"
  else:
    assert veri
    exe = "build/VeribetrfsYcsb"

  make_options = ""
  if log_stats:
    make_options += "LOG_QUERY_STATS=1 "
  if use_unverified_row_cache:
    make_options += "WANT_UNVERIFIED_ROW_CACHE=true "
      
  actuallyprint("Building executable...")
  sys.stdout.flush()
  #cmd = make_options + "make " + exe + " -j4 > /dev/null 2> /dev/null"
  cmd = make_options + "make " + exe
  actuallyprint(cmd)
  ret = os.system(cmd)
  assert ret == 0

  workload_cmd = " ".join(workload.split(","))

  if device == "ssd":
    loc = "/tmp/veribetrfs"
  elif device == "disk":
    #loc = "/home/tjhance/ycsb/"
    loc = "/mnt/xvde/scratch"
  else:
    assert False

  print("Device type: " + device)
  print("Using " + loc)

  ret = os.system("rm -rf " + loc)
  assert ret == 0
  ret = os.system("mkdir " + loc)
  assert ret == 0

  if rocks:
    loc = loc
  elif berkeley:
    loc = loc + "/berkeley.db"
  elif kyoto:
    loc = loc + "/kyoto.cbt"
  else:
    assert veri
    loc = loc + "/veribetrkv.img"

  if from_archive:
    if rocks:
      os.system("cp -a " + from_archive + "/* " + loc + "/")
    else:
      os.system("cp -a " + from_archive + " " + loc)
    
  driver_options = ""
  if use_filters:
    driver_options += "--filters "
  if from_archive:
    driver_options += "--preloaded "

  clear_page_cache()

  # bitmask indicating which CPUs we can use
  # See https://linux.die.net/man/1/taskset
  taskset_cmd = "taskset 4 "

  cgroup_prefix = "cgexec -g memory:VeribetrfsExp " if cgroup_enabled else ""
  command = taskset_cmd + cgroup_prefix + "./" + exe + " " + loc + " " + driver_options + " " + workload_cmd
  actuallyprint(command)
  sys.stdout.flush()

  start_time = time.time()
  end_time = start_time + time_budget_sec
  proc = subprocess.Popen(command, shell=True, preexec_fn=os.setsid, stdout=fp)
  proc_grp_id = os.getpgid(proc.pid)
  actuallyprint("experiment pid %d pgid %d" % (proc.pid, proc_grp_id))
  while proc.poll() == None:
    if time.time() >= end_time:
      os.killpg(proc_grp_id, signal.SIGKILL)
      actuallyprint("time_budget exhausted; killed.")
      break
    time.sleep(10)

  assert ret == 0

if __name__ == "__main__":
  main()
