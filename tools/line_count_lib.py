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

# We'll leave copies of counted files here so we can inspect the counting filters for sanity.
INSPECT_DIR = "./build/inspect"

class Counter:
    def __init__(self, iron_base):
        self.iron_base = iron_base

    def run_dafny(self, show_ghost, dafny_filename, tmp_filename):
      executable = self.iron_base + "/.dafny/dafny/Binaries/dafny"
      args  = [] 
      args += ["/rprint:-"]
      args += ["/noAutoReq"]
      args += ["/noVerify"]
      args += ["/compile:0"]
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
      #print(" ".join(cmd))
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

    # Remove detritus from running Dafny
    def clean_dafny_output(self, filename, inspect_path):
      program = open(filename).read()#.decode("utf-8")

      program = self.remove_warnings(program)
      program = self.remove_paired_comments(program)
      program = self.remove_cruft(program)
      program = self.remove_whitespace(program)

      open(filename, "w").write(program)
      try:
        os.makedirs(os.path.dirname(inspect_path))
      except FileExistsError:
        pass
      print("inspect at %s" % inspect_path)
      open(inspect_path, "w").write(program)

    def remove_warnings(self, program):
      """strip out stdout gunk from running Dafny."""
      lines = program.split("\n")
      clean = []
      for line in lines:
        if line.startswith("Dafny program verifier finished"):
          pass
        elif re.search("Warning: .*No terms found", line):
          pass
        elif re.search("Warning: the type of the other operand", line):
          pass
        else:
          clean.append(line)
      return "\n".join(clean)

    def remove_paired_comments(self, program):
      """Dafny emits annotations as /*blah /*blah*/ blah*/, and sloccount counts it wrong."""
      regions = re.compile("(/\*|\*/)").split(program)
      depth = 0
      output = []
      for i in range(len(regions)):
        region = regions[i]
        if region=="/*":
          depth+=1
        elif region=="*/":
          depth-=1
        else:
          #print("  "*depth, region.replace("\n", "_"))
          if depth==0:
            output.append(region)
      return "".join(output)

    def remove_cruft(self, program):
      # import, export, provides?
      # lines with only braces?
      lines = program.split("\n")
      clean = []
      for line in lines:
        if (re.search("^\s*export ", line)
            or re.search("^\s*provides ", line)
            or re.search("^\s*reveals ", line)
            or re.search("^\s*import ", line)):
          # Maybe these export controls should get billed, but it's unclear
          # (from out here in this python script) who to bill them to: some
          # of the symbols are ghosty, others are methods. So I'm going to
          # hide them all, so that the ratios of the actual type and
          # function, method declarations tell the story with less noise.
          #print("hiding ", line)
          pass
        else:
          clean.append(line)
      return "\n".join(clean)

    def remove_whitespace(self, program):
      lines = program.split("\n")
      clean = []
      for line in lines:
        if re.search("^\s*$", line):
          pass
        else:
          clean.append(line)
      return "\n".join(clean)

    def compute_sloc(self, show_ghost, dafny_file):
      tmp_dir = self.make_tmp_dir()
      dafny_dir = os.path.dirname(dafny_file)
      dafny_base = os.path.basename(dafny_file)
      # jonh: name the dafny output .cs to get sloccount to count it.
      tmp_filename = "%s-%s.cs" % (dafny_base, ("ghost" if show_ghost else "real"))
      tmp_file = os.path.join(tmp_dir, tmp_filename)

      self.run_dafny(show_ghost, dafny_file, tmp_file)
      inspect_path = os.path.join(os.path.join(INSPECT_DIR, dafny_dir), tmp_filename)
      self.clean_dafny_output(tmp_file, inspect_path)
      sloc = self.run_sloccount(tmp_dir)

      os.remove(tmp_file)
      os.rmdir(tmp_dir)

      return int(sloc)

    def make_tmp_dir(self):
      tmp_dir = self.iron_base + "/build/linecounts_%x" % random.randint(0, 1<<31)
      if not os.path.exists(tmp_dir):
        os.makedirs(tmp_dir)
      #print("tmp dir: %s" % tmp_dir)
      return tmp_dir

    def collect_line_counts(self, dafny_files):
      for f in dafny_files:
        ghost_sloc = self.compute_sloc(True, f.filename)

        if f.is_spec():
          f.spec = ghost_sloc
          f.verify_time = 0
        else:
          impl_sloc = self.compute_sloc(False, f.filename)
          f.impl = impl_sloc
          f.proof = ghost_sloc - impl_sloc
