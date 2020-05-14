#!/usr/bin/python3

from automation import *
from suite import *

common_vars = [
    Variable("ram", "run_veri", [Value("2gb", "ram=2.0gb")]),
    Variable("device", "run_veri", [Value("disk", "device=disk")]),
    Variable("workload", "run_veri", [Value("wka6m", "workload=ycsb/wka-uniform-rc6000k.spec")]),
    Variable("duration", "run_veri", [Value("1h", "time_budget=1h")]),
    ]
veri_suite = Suite(
    "veri",
    Variable("git_branch", "git_branch", [Value("page", "page-la2")]),
    Variable("system", "run_veri", [Value("veri64k", "config-64kb")]),
    Variable("nodeCountFudge", "run_veri", [Value(str(f), "nodeCountFudge="+str(f)) for f in [0.8,0.9,1.0,1.1,1.2,1.3]]),
    *common_vars)
blocks_suite = Suite(
    "recordcount-page-22",
    Variable("git_branch", "git_branch", [Value("block", "leak-adventure-2")]),
    Variable("system", "run_veri", [Value("rocks", "rocks"), Value("veri64k", "config-64kb")]),
    *common_vars)
suite = ConcatSuite("recordcount-page-22", veri_suite, blocks_suite)

RUN_VERI_PATH="tools/run-veri-config-experiment.py"

def cmd_for_idx(idx, worker):
    variant = suite.variants[idx]
    cmd = (ssh_cmd_for_worker(worker) + [
        "cd", "veribetrfs", ";",
        "sh", "tools/clean-for-build.sh", variant.git_branch(), ";",
        ]
        + [RUN_VERI_PATH] + variant.run_veri_params() + ["output=../"+variant.outfile()]
        )
    return cmd

def main():
    set_logfile(suite.logpath())
    log("PLOT tools/aws/pull-results.py && %s && eog %s" % (suite.plot_command(), suite.png_filename()))
    log("VARIANTS %s" % suite.variants)

    workers = retrieve_running_workers()
    worker_pipes = launch_worker_pipes(workers, len(suite.variants), cmd_for_idx, dry_run=True)
    monitor_worker_pipes(worker_pipes)

main()
