#!/usr/bin/python3

from automation import *
from suite import *

common_vars = [
    Variable("seed", "run_map", [
        Value("seed0", "seed=348725789"),
        Value("seed1", "seed=34578699348"),
        Value("seed2", "seed=23945765203"),
        Value("seed3", "seed=625478238923"),
        Value("seed4", "seed=657843290874"),
        Value("seed5", "seed=9526729840202"),
        ]),
    ]
repr_suite = Suite(
    "repr",
    Variable("git_branch", "git_branch", [Value("master", "eval-btree-master")]),
    *common_vars)
linear_suite = Suite(
    "linear",
    Variable("git_branch", "git_branch", [Value("linear", "eval-btree-linear")]),
    *common_vars)
suite = ConcatSuite("mutablemap-new", linear_suite, repr_suite)

MBTREE_PATH="./tools/run-map-config-experiment.py"

def cmd_for_idx(idx, worker):
    variant = suite.variants[idx]
    cmd = (ssh_cmd_for_worker(worker) + [
        "cd", "veribetrfs", ";",
        "git", "clean", "-fd", ".", ";",
        "sh", "tools/clean-for-build.sh", variant.git_branch(), ";",
        ] + ["python3", MBTREE_PATH] + ["git_branch=" + variant.git_branch()] + [variant.valmap[var].param_value for var in variant.vars_of_type("run_map")] + ["output=../"+variant.outfile()]
        )
    return Command(str(variant), cmd)

def main():
    set_logfile(suite.logpath())
    log("PLOT tools/aws/pull-results.py")
    log("VARIANTS %s" % suite.variants)

    workers = retrieve_running_workers()
    worker_pipes = launch_worker_pipes(workers, len(suite.variants), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
