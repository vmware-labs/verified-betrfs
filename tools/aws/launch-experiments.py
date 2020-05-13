#!/usr/bin/python3

from automation import *
from suite import *

suite = Suite(
    "recordcount-page-13",
    Variable("git_branch", "git_branch", [Value("page", "page-la2"), Value("block", "leak-adventure-2")]),
    Variable("system", "run_veri", [Value("rocks", "rocks"), Value("veri64k", "config-64kb")]),
    Variable("ram", "run_veri", [Value("2gb", "ram=2.0gb")]),
    Variable("device", "run_veri", [Value("disk", "device=disk")]),
    Variable("workload", "run_veri", [Value("wka1m", "workload=ycsb/wka-uniform-rc1000k.spec")]),
    Variable("duration", "run_veri", [Value("1h", "time_budget=1h")]),
    )

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
    log("PLOT %s" % suite.plot_command())
    log("VARIANTS %s" % suite.variants)

    workers = retrieve_running_workers()
    worker_pipes = launch_worker_pipes(workers, len(suite.variants), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
