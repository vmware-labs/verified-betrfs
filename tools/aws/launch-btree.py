#!/usr/bin/python3

from automation import *
from suite import *

common_vars = [
    Variable("ops", "run_btree", [
        Value("2pow{}".format(pp), "ops={}".format(2**pp)) for pp in [20, 21, 22, 23, 24, 25, 26, 27]]),
    ]
repr_suite = Suite(
    "repr",
    Variable("git_branch", "git_branch", [Value("master", "eval-btree-master")]),
    *common_vars)
linear_suite = Suite(
    "linear",
    Variable("git_branch", "git_branch", [Value("linear", "eval-btree-linear")]),
    *common_vars)
suite = ConcatSuite("andreal-btree-01", repr_suite)

MBTREE_PATH="./tools/run-btree-config-experiment.py"

def cmd_for_idx(idx, worker):
    variant = suite.variants[idx]
    cmd = (ssh_cmd_for_worker(worker) + [
        "cd", "veribetrfs", ";",
        "git", "clean", "-fd", ".", ";",
        "sh", "tools/clean-for-build.sh", variant.git_branch(), ";",
        ] + ["python3", MBTREE_PATH] + [variant.valmap[var].param_value for var in variant.vars_of_type("run_btree")] + ["output=../"+variant.outfile()]
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
