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

def autoconfig(bucket_weight_bytes, cache_size_bytes):
  cache_size_nodes = int(cache_size_bytes // bucket_weight_bytes)
    
  return [
    ("MaxTotalBucketWeightUint64", str(bucket_weight_bytes)),
    ("MaxCacheSizeUint64", str(cache_size_nodes)),
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

class Blktrace:
  def __init__(self):
    self.cleanall()
    self.killall()

  def cleanall(self):
    actuallyprint("Blktrace.cleanall")
    os.system("rm xvde.blktrace.*") # XXX hacky hack

  def killall(self):
    actuallyprint("Blktrace.killall")
    subprocess.call(["sudo", "killall", "blktrace"])

  def start(self, device):
    actuallyprint("Blktrace.start")
    self.blktrace_process = subprocess.Popen(
        ["sudo", "blktrace", device], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  
  def stop(self):
    actuallyprint("Blktrace.stop")
    self.killall()
    actuallyprint("Blktrace.wait")
    self.blktrace_process.wait()

    actuallyprint("Blktrace.emit")
    (stdout,stderr) = self.blktrace_process.communicate()
    lines = (stdout.decode("utf-8") + stderr.decode("utf-8")).split("\n")
    for line in lines:
      #fp.write("blktrace "+line+"\n") overwrites all collected data; and besides it's in the log.
      sys.stdout.write("blktrace "+line+"\n")
    actuallyprint("Blktrace.done")

def main():
  git_branch = None
  archive_dir = "/mnt/xvde/archives"
  workload = None
  device = None
  mem = None
  value_updates = []
  config = None
  log_stats = False
  max_children = None   # Default
  cgroup_enabled = True
  use_unverified_row_cache = None
  use_filters = None
  from_archive = None
  nodeCountFudge           = None  # Pretend we have more memory when computing node count budget, since mean node is 75% utilized. This lets us tune veri to exploit all available cgroup memory.
  veri_cache_size_in_bytes = None
  veri_cache_size_in_nodes = None
  veri_bucket_weight       = None
  veri_log_size_in_blocks  = None
  veri_o_direct            = None
  
  veri = None
  rocks = None
  berkeley = None
  kyoto = None
  time_budget_sec = 3600*24*365 # You get a year if you don't ask for a budget

  fp = None

  for arg in sys.argv[1:]:
    if arg.startswith("ram="):
      ram = arg[len("ram=") : ]
    elif arg.startswith("git_branch="):
        git_branch = arg[len("git_branch=") : ]
    elif arg.startswith("workload="):
      workload = arg[len("workload=") : ]
    elif arg.startswith("device="):
      device = arg[len("device=") : ]
    elif arg.startswith("fromArchive="):
      from_archive = arg[len("fromArchive=") : ]
    # elif arg.startswith("nodeCountFudge="):
    #   nodeCountFudge = float(arg[len("nodeCountFudge=") : ])
    elif arg.startswith("cacheSizeInBytes="):
      veri_cache_size_in_bytes = int(arg[len("cacheSizeInBytes=") : ])
    elif arg.startswith("cacheSizeInNodes="):
      veri_cache_size_in_nodes = int(arg[len("cacheSizeInNodes=") : ])
    elif arg.startswith("bucketWeight="):
      veri_bucket_weight = int(arg[len("bucketWeight=") : ])
    elif arg.startswith("veriLogSizeInBlocks="):
      veri_log_size_in_blocks = int(arg[len("veriLogSizeInBlocks=") : ])
    elif arg == "veriUseODirect":
        veri_o_direct = True
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
  assert git_branch is not None
  
  assert veri_cache_size_in_bytes is None or veri_cache_size_in_nodes is None
  assert veri_cache_size_in_bytes is None or veri_bucket_weight is not None
  assert veri_bucket_weight is None or veri
  
  assert workload != None
  assert device != None

  assert veri or rocks or berkeley or kyoto

  if use_unverified_row_cache:
      assert veri

  if veri_o_direct:
      assert veri
      
  if use_filters:
      assert rocks

  actuallyprint("Experiment time budget %s" % (datetime.timedelta(seconds=time_budget_sec)))
  actuallyprint("metadata time_budget %s seconds" % time_budget_sec)

  if veri_cache_size_in_bytes:
      veri_cache_size_in_nodes = veri_cache_size_in_bytes // veri_bucket_weight
      
  if veri_bucket_weight is not None:
      value_updates = value_updates + [ ("MaxTotalBucketWeightUint64", str(veri_bucket_weight)) ]
  if veri_cache_size_in_nodes is not None:
      value_updates = value_updates + [ ("MaxCacheSizeUint64", str(veri_cache_size_in_nodes)) ]
  if veri_log_size_in_blocks is not None:
      value_updates = value_updates + [ ("DiskNumJournalBlocksUint64", str(veri_log_size_in_blocks)) ]
      
  if rocks:
    exe = "build/RocksYcsb"
  elif berkeley:
      exe = "build/BerkeleyYcsb"
  elif kyoto:
      exe = "build/KyotoYcsb"
  else:
    assert veri
    exe = "build/VeribetrfsYcsb"

  if device == "ssd":
    datadir = "/tmp/veribetrfs"
  elif device == "disk":
    #loc = "/home/tjhance/ycsb/"
    datadir = "/mnt/xvde/scratch"
  else:
    assert False

  print("Device type: " + device)
  print("Using " + datadir)

  if rocks:
    loc = datadir
  elif berkeley:
    loc = datadir + "/berkeley.db"
  elif kyoto:
    loc = datadir + "/kyoto.cbt"
  else:
    assert veri
    loc = datadir + "/veribetrkv.img"

  driver_options = ""
  if use_filters:
    driver_options += "--filters "
  if from_archive:
    driver_options += "--preloaded "

  workload_cmd = " ".join(workload.split(","))

  make_options = ""
  if log_stats:
    make_options += "LOG_QUERY_STATS=1 "
  if use_unverified_row_cache:
    make_options += "WANT_UNVERIFIED_ROW_CACHE=true "

  make_options = ""
  
  if veri_o_direct == True:
      make_options = make_options + " WANT_O_DIRECT=true "
  
  cgroup_defaults()
  if ram != None:
    set_mem_limit(ram)

  ret = os.system("rm -rf build/")
  assert ret == 0

  ret = os.system("./tools/clean-for-build.sh " + git_branch)
  assert ret == 0
  
  if veri:
    print("Building Bundle.cpp...")
    ret = os.system("make " + make_options + " build/Bundle.cpp > /dev/null 2> /dev/null")
    assert ret == 0

  for (name, value) in value_updates:
    assert veri
    print("setting " + name + " to " + value)
    splice_value_into_bundle(name, value)

  actuallyprint("Building executable...")
  sys.stdout.flush()
  #cmd = make_options + "make " + exe + " -j4 > /dev/null 2> /dev/null"
  cmd = make_options + "make " + make_options + " " + exe
  actuallyprint(cmd)
  ret = os.system(cmd)
  assert ret == 0

  ret = os.system("rm -rf " + datadir)
  assert ret == 0
  ret = os.system("mkdir -p " + datadir)
  assert ret == 0

  if from_archive:
    if rocks:
      os.system("cp -a " + from_archive + "/* " + datadir + "/")
    else:
      os.system("cp -a " + from_archive + " " + loc)
  elif veri:
      os.system("head -c 17179869184 /dev/zero > " + loc)
      
  clear_page_cache()

  os.system("iostat")

  blktrace = Blktrace()
  blktrace.start("/dev/xvde")   # alert jonh hack hardcoded blktrace device
  
  # bitmask indicating which CPUs we can use
  # See https://linux.die.net/man/1/taskset
  taskset_cmd = "taskset 4 "
  cgroup_prefix = "cgexec -g memory:VeribetrfsExp " if cgroup_enabled else ""
  command = taskset_cmd + cgroup_prefix + "time ./" + exe + " " + loc + " " + driver_options + " " + workload_cmd
  actuallyprint(command)
  sys.stdout.flush()

  proc = subprocess.Popen(command, shell=True, preexec_fn=os.setsid, stdout=fp)
  proc_grp_id = os.getpgid(proc.pid)
  actuallyprint("experiment pid %d pgid %d" % (proc.pid, proc_grp_id))
  try:
    ret = proc.wait(timeout = time_budget_sec)
  except TimeoutExpired:
    actuallyprint("timeout expired (%ds); killing" % time_budget_set)
    proc.kill()
    ret = proc.wait(timeout = 10)

  actuallyprint("main blktrace stop");
  blktrace.stop()
  actuallyprint("main blktrace stopped");

  assert ret == 0
  os.system("iostat")
  actuallyprint("done")

if __name__ == "__main__":
  main()
