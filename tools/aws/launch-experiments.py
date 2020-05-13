#!/usr/bin/python3

import os
import subprocess
from automation import *

#control = "tools/run-veri-config-experiment.py workload=ycsb/wka-uniform.spec device=disk ram=2.0gb pillow=1.1 time_budget=1h config-64kb"
#experiments = [("max_children=%d" % x) for x in (8,12,16,20,32)]

#control = "tools/run-veri-config-experiment.py workload=ycsb/wka-uniform.spec device=disk ram=2.0gb pillow=1.1 time_budget=1h"
#experiments = [["rocks"], ["config-64kb"], ["config-1mb"], ["config-8mb"]]
#label="blocksize-sweep-01"

control = "tools/run-veri-config-experiment.py device=disk ram=2.0gb time_budget=1h"
workloads=["workload=ycsb/wka-uniform-rc%sk.spec"%sz for sz in (400,1000,2000)]
git_branch="page-la2"
#configs=["rocks", "config-64kb"]
configs=["config-64kb"]
experiments = []
for w in workloads:
    for c in configs:
        experiments.append([w,c])
label="recordcount-page-08"

#machine_indices = [5]

def curt_label_for(exp):
    return "-".join([p.replace("=", ":").replace('/', '_') for p in exp])

def outfile_for(exp):
    return "expresults/%s-%s.data" % (label, curt_label_for(exp))

def plot_command_for(experiments):
    return " ".join([
        "tools/plot/perf-compare.py",
        "output=%s.png" % label] + [curt_label_for(exp)+"="+outfile_for(exp) for exp in experiments])

def cmd_for_idx(idx, worker):
    exp = experiments[idx]
    cmd = ssh_cmd_for_worker(worker) + [
        "cd", "veribetrfs", ";",
        "tools/clean-for-build.sh", git_branch, ";"
    ] + control.split() + exp + ["output=../"+outfile_for(exp)]
    return cmd

def main():
    set_logfile(os.path.join("logs", label+".log"))
    log(plot_command_for(experiments))

    workers = retrieve_running_workers()
    #print("workers: ", workers)
    worker_pipes = launch_worker_pipes(workers, len(experiments), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
