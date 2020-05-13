#!/usr/bin/python3

import subprocess
from automation import *

#control = "tools/run-veri-config-experiment.py workload=ycsb/wka-uniform.spec device=disk ram=2.0gb pillow=1.1 time_budget=1h config-64kb"
#experiments = [("max_children=%d" % x) for x in (8,12,16,20,32)]

#control = "tools/run-veri-config-experiment.py workload=ycsb/wka-uniform.spec device=disk ram=2.0gb pillow=1.1 time_budget=1h"
#experiments = [["rocks"], ["config-64kb"], ["config-1mb"], ["config-8mb"]]
#label="blocksize-sweep-01"

control = "tools/run-veri-config-experiment.py workload=ycsb/wka-uniform.spec device=disk ram=2.0gb pillow=1.1 time_budget=1h"
workloads=["workload=wka-uniform-rc%sk.spec"%sz for sz in (400,1000,2000)]
git_branch="page-la2"
configs=["rocks", "config-64kb"]
experiments = []
for w in workloads:
    for c in configs:
        experiments.append([w,c])
label="recordcount-sweep-01"

#machine_indices = [5]

def curt_label_for(exp):
    return "-".join([p.replace("=", ":") for p in exp])

def outfile_for(exp):
    return "expresults/%s-%s.data" % (label, curt_label_for(exp))

def plot_command_for(experiments):
    return " ".join([
        "tools/plot/perf-compare.py",
        "output=%s.png" % label] + [curt_label_for(exp)+"="+outfile_for(exp) for exp in experiments])

def launch_worker_pipes(experiments, workers):
    worker_pipes = []
    for expi in range(len(experiments)):
        exp = experiments[expi]
        worker = workers[expi]

        cmd = ssh_cmd_for_worker(worker) + [
                "cd", "veribetrfs", ";",
                "git", "checkout", git_branch, ";",
                "git", "pull", ";",
                "tools/update-submodules.sh", ";",
                "tools/update-dafny.sh", ";",
                "make", "clean", ";",
                ] + control.split() + exp + ["output=../"+outfile_for(exp)]
        print("launching worker %d on %s: %s" % (expi, worker["Name"], " ".join(cmd)))
        worker_pipe = subprocess.Popen(cmd)
        worker_pipes.append(worker_pipe)
    return worker_pipes

def main():
    print(plot_command_for(experiments))

    workers = retrieve_running_workers()
    #print("workers: ", workers)
    assert len(experiments) <= len(workers)
    worker_pipes = launch_worker_pipes(experiments, workers)
    monitor_worker_pipes(worker_pipes)
    print("All jobs complete.")

main()
