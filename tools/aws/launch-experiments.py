#!/usr/bin/python3

from automation import *
from suite import *

common_vars = [
    Variable("ram", "run_veri", [Value("2gb", "ram=2.0gb")]),
    Variable("device", "run_veri", [Value("disk", "device=disk")]),
    Variable("workload", "run_veri", [Value("wkc", "workload=ycsb/workloadc-onefield.spec")]),
    Variable("duration", "run_veri", [Value("30m", "time_budget=30m")]),
#    Variable("replica", "silent", [Value("r0", "r=0"), Value("r1", "r=1")]),
    ]
veri_suite = Suite(
    "veri",
    #Variable("git_branch", "git_branch", [Value("dynamic-frames", "osdi20-artifact-dynamic-frames"), Value("linear", "osdi20-artifact-linear")]),
    Variable("git_branch", "git_branch", [Value("row-cache-adventure", "row-cache-adventure")]),
    Variable("row_cache", "run_veri", [
        Value("0i", "env:ROW_CACHE_SIZE=1"),
        Value("12i", "env:ROW_CACHE_SIZE=4096"),
        Value("15i", "env:ROW_CACHE_SIZE=32768"),
        Value("18i", "env:ROW_CACHE_SIZE=262144"),
        Value("21i", "env:ROW_CACHE_SIZE=2097152"),
        ]),
    Variable("nodeCountFudge", "run_veri", [Value(str(f), "nodeCountFudge="+str(f)) for f in [0.5]]),
#    Variable("system", "run_veri", [Value("veri2m", "config-2mb")]),
#    Variable("max_children", "run_veri", [Value("fanout16", "max_children=16")]),
    Variable("veri", "run_veri", [Value("veri", "veri")]),
    Variable("cgroup", "run_veri", [Value("yescgroup", "cgroup=True")]),
    *common_vars)
rocks_suite = Suite(
    "rocks",
    Variable("git_branch", "git_branch", [Value("la2", "leak-adventure-2")]),
    Variable("system", "run_veri", [Value("rocks", "rocks")]),
    *common_vars)
#suite = ConcatSuite("robj-010", veri_suite, rocks_suite)
suite = ConcatSuite("row-cache-003", veri_suite)

RUN_VERI_PATH="tools/run-veri-config-experiment.py"

def cmd_for_idx(idx, worker):
    variant = suite.variants[idx]
    cmd = (ssh_cmd_for_worker(worker) + [
        "cd", "veribetrfs", ";",
        "sh", "tools/clean-for-build.sh", variant.git_branch(), ";",
        ]
        + [RUN_VERI_PATH] + variant.run_veri_params() + ["output=../"+variant.outfile()]
        )
    return Command(str(variant), cmd)

def main():
    set_logfile(suite.logpath())
    log("PLOT tools/aws/pull-results.py && %s && eog %s" % (suite.plot_command(), suite.png_filename()))
    log("VARIANTS %s" % suite.variants)

    workers = retrieve_running_workers()
    worker_pipes = launch_worker_pipes(workers, len(suite.variants), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
