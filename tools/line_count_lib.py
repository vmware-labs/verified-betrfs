# Definitions from IronFleet to ensure that results are comparable.
# Based on:
# https://github.com/microsoft/Ironclad/blob/master/ironfleet/tools/scripts/dafny-line-count.py
# ...with improvements and refactoring to generalize to a new code base and
# different build system.

import os
import re
import shutil
import subprocess
import random

class DafnyFile:
  def __init__(self, filename, verify_time):
    self.filename = filename.replace('\\', '/')
    self.verify_time = verify_time
    self.spec = 0
    self.impl = 0
    self.proof = 0
    
  def __repr__(self):
    return "%s %s secs %s spec %s impl %s proof" % (self.filename, self.verify_time, self.spec, self.impl, self.proof)

  def is_spec(self):
    return self.filename.endswith(".s.dfy")

class Counter:
    def __init__(self, iron_base):
        self.iron_base = iron_base

    def run_dafny(self, show_ghost, dafny_filename, tmp_filename):
      executable = self.iron_base + "/.dafny/dafny/Binaries/dafny"
      args  = [] 
      args += ["/rprint:-"]
      args += ["/noAutoReq"]
      args += ["/noVerify"]
      args += ["/nologo"]
      args += ["/env:0"]
      if show_ghost:
        args += ["/printMode:NoIncludes"]
      else:
        args += ["/printMode:NoGhost"]
      args += [dafny_filename]

      tmp_file = open(tmp_filename, "w")
      #print [executable] + args
      subprocess.call([executable] + args, shell=False, stdout=tmp_file)
      tmp_file.close()

    # Remove detritus from running Dafny
    def clean_dafny_output(self, filename):
      file = open(filename, "r")
      clean = ""
      for line in file.readlines():
        if line.startswith("Dafny program verifier finished"):
          pass
        else:
          clean += line + "\n"
      file.close()
      file = open(filename, "w")
      file.write(clean)
      file.close()

    def run_sloccount(self, tmp_dir):
      data_dir = tmp_dir + "_data"
      os.makedirs(data_dir)
      executable = "sloccount"
      args  = [] 
      args += ["--datadir"]
      args += [data_dir]
      args += ["--details"]
      args += [tmp_dir]

      sloc = -1
      #print [executable] + args
      cmd = [executable] + args
      output = subprocess.check_output(cmd) #, shell=True)
      output = output.decode("utf-8")
      for line in output.split('\n'):
        result = re.search("(\d+)\s+cs", line)  # TODO(jonh): hack dfy->cs
        if result:
          sloc = result.group(1)
      if sloc == -1:
        print("pid %d sloc cmd: >> %s <<" % (os.getpid(), " ".join(cmd)))
        print("pid %d sloc output: >>%s<<" % (os.getpid(), output))
        raise Exception("Failed to find sloccount result! in %s" % tmp_dir)
      shutil.rmtree(data_dir)
      return sloc

    def compute_sloc(self, show_ghost, dafny_file, tmp_dir):
      tmp_file = tmp_dir + "/tmp.cs"    # TODO(jonh): hack to get sloccount to see dfy file

      self.run_dafny(show_ghost, dafny_file, tmp_file)
      self.clean_dafny_output(tmp_file)
      sloc = self.run_sloccount(tmp_dir)
      os.remove(tmp_file)

      return int(sloc)

    def collect_line_counts(self, dafny_files):
      tmp_dir = self.iron_base + "/tmp/linecounts_%x" % random.randint(0, 1<<31)

      if not os.path.exists(tmp_dir):
        os.makedirs(tmp_dir)
      
      for f in dafny_files:
        ghost_sloc = self.compute_sloc(True, f.filename, tmp_dir)

        if f.is_spec():
          f.spec = ghost_sloc
          f.verify_time = 0
        else:
          impl_sloc = self.compute_sloc(False, f.filename, tmp_dir)
          f.impl = impl_sloc
          f.proof = ghost_sloc - impl_sloc
      os.rmdir(tmp_dir)
