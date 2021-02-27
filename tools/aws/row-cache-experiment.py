#!/usr/bin/python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT


from automation import *
from suite import *

parser = argparse.ArgumentParser(parents=[automation_argparser])
args = parser.parse_args()

common_vars = [
    Variable("infrastructure_branch", "infrastructure_branch",
        [Value("aws-tweaks", "aws-tweaks")]),
    Variable("ram", "run_veri", [Value("2gb", "ram=2.0gb")]),
    Variable("bucketWeight", "run_veri", [Value("bw", "bucketWeight=2031616")]),
    Variable("device", "run_veri", [Value("disk", "device=disk")]),
    Variable("workload", "run_veri", [Value("wkc", "workload=ycsb/workloada-onefield.spec,ycsb/workloadc-big.spec")]),
    Variable("duration", "run_veri", [Value("90m", "time_budget=90m")]),
    Variable("replica", "silent", [Value("r%d"%r, "r=%d"%r) for r in range(3)]),
    ]
veri_suite = Suite(
    "veri",
    Variable("git_branch", "run_veri", [Value("row-cache-adventure", "git_branch=row-cache-adventure")]),
    Variable("row_cache", "run_veri", [Value("0", "env:ROW_CACHE_SIZE=0")] + [
        Value("%di" % bi,
            "env:ROW_CACHE_SIZE=%d" % (1<<bi)) for bi in [9, 14, 19]]),
    Variable("cache_size", "run_veri", [Value("cache100nodes", "cacheSizeInNodes=100")]),
#    Variable("system", "run_veri", [Value("veri2m", "config-2mb")]),
#    Variable("max_children", "run_veri", [Value("fanout16", "max_children=16")]),
    Variable("veri", "run_veri", [Value("veri", "veri")]),
    Variable("cgroup", "run_veri", [Value("yescgroup", "cgroup=True")]),
    *common_vars)
#rocks_suite = Suite(
#    "rocks",
#    Variable("git_branch", "git_branch", [Value("la2", "leak-adventure-2")]),
#    Variable("system", "run_veri", [Value("rocks", "rocks")]),
#    *common_vars)
suite = ConcatSuite("row-cache-035", veri_suite)

RUN_VERI_PATH="tools/run-veri-config-experiment.py"

def cmd_for_idx(idx, worker):
    variant = suite.variants[idx]
    cmd = (ssh_cmd_for_worker(worker) + [
        "cd",  "veribetrfs", ";",
        "git", "fetch", ";",
        "git", "checkout", variant.infrastructure_branch(), ";",
        "git", "pull", ";",
        #"sh",  "tools/clean-for-build.sh", variant.git_branch(), ";",
        ]
        + [RUN_VERI_PATH] + variant.run_veri_params() + ["output=../"+variant.outfile()]
        )
    return Command(str(variant), cmd)

def main():
    set_logfile(suite.logpath())
    log("PLOT tools/aws/pull-results.py && %s && eog %s" % (suite.plot_command(), suite.png_filename()))
    log("VARIANTS %s" % suite.variants)

    workers = retrieve_running_workers(workers_file=args.workers_file, ssd=args.ssd)
    worker_pipes = launch_worker_pipes(workers, len(suite.variants), cmd_for_idx, dry_run=args.dry_run)
    monitor_worker_pipes(worker_pipes)

main()
