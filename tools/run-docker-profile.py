#!/usr/bin/env python3
# todo refactor with run-docker-dafny
import sys
import os
import subprocess

my_dir = os.path.dirname(__file__)
root_dir = os.path.abspath(os.path.join(my_dir, ".."))
cur_dir = os.getcwd()
prefix = os.path.commonprefix([cur_dir, root_dir])
if root_dir != prefix:
    sys.stderr.write(f"This script only works for files reachable from {root_dir}\n")
    # Because of the way we mount the host filesystem into docker
    sys.exit(-1)
#print(f"prefix {prefix}")
#print(f"root_dir {root_dir}")

# Where root_path will appear inside container
mount_point="/home/work_dir"
# Working dir to use once inside container
rel_path = os.path.relpath(cur_dir, root_dir)

# USERNAME used to identify docker container built by build-docker-dafny.sh
username = os.getenv("USERNAME")

cmd = [
    "docker",
    "container",
    "run",
    "--mount",
    f"src={root_dir},target={mount_point},type=bind,readonly",
    "-w",
    os.path.join(mount_point, rel_path),
    "-t",
    f"{username}/dafny",
    "/home/work_dir/tools/dafny-profile.py",
    ] + sys.argv[1:]
print(" ".join(cmd))
subprocess.call(cmd)
