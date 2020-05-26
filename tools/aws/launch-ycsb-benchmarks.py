#!/usr/bin/python3

from automation import *
from suite import *

replica_count = 6

common_vars = [
    Variable("cgroup",     "run_veri",   [Value("yescgroup", "cgroup=True")]),
    Variable("ram",        "run_veri",   [Value("2gb",       "ram=2.0gb")]),
    Variable("device",     "run_veri",   [Value("disk",      "device=disk")]),
    Variable("workload",   "run_veri",
             [Value("all", "workload=" + ",".join(
                    ["ycsb/workloada-onefield.spec", # load
                    "ycsb/workloadc-uniform.spec"  , # Doesn't modify database, so sneak it in here
                    "ycsb/workloada-onefield.spec" , # runs...
                    "ycsb/workloadb-onefield.spec" ,
                    "ycsb/workloadc-onefield.spec" ,
                    "ycsb/workloadd-onefield.spec" ,
                    "ycsb/workloadf-onefield.spec" ,
                    ])),]),
    #Variable("duration", "run_veri", [Value("2h", "time_budget=2h")]),
    Variable("replica",  "silent", [Value("r{}".format(r), "r={}".format(r)) for r in range(replica_count)]),
    ]
veri_suite = Suite(
    "veribetrkv",
    Variable("git_branch", "git_branch", [
        Value("master",    "master"),
        Value("linear",    "linear-disintegration"),
        ]),
    Variable("system",     "run_veri", [Value("veri", "veri")]),
    Variable("rowcache",   "run_veri", [Value("norowcache", ""),
                                        Value("yesrowcache", "use_unverified_row_cache")]),
    *common_vars)

common_vars_others = common_vars + [
    Variable("git_branch", "git_branch", [Value("master",    "master")]),
    ]

rocks_suite = Suite(
    "rocksdb",
    Variable("system",  "run_veri", [Value("rocks", "rocks")]),
    Variable("filters", "run_veri", [Value("nofilters", ""),
                                     Value("yesfilters", "use_filters")]),
    *common_vars_others)
berkeley_suite = Suite(
    "berkeleydb",
    Variable("system", "run_veri", [Value("berkeley", "berkeley")]),
    *common_vars_others)
kyoto_suite = Suite(
    "berkeleydb",
    Variable("system", "run_veri", [Value("kyoto", "kyoto")]),
    *common_vars_others)
#suite = ConcatSuite("ycsb-001", veri_suite, rocks_suite, berkeleydb_suite)
suite = ConcatSuite("silver-run-berkeley-ssd", berkeley_suite)

RUN_VERI_PATH="tools/run-veri-config-experiment.py"

def cmd_for_idx(idx, worker):
    variant = suite.variants[idx]
    cmd = (ssh_cmd_for_worker(worker) + [
        "cd", "veribetrfs", ";",
        "sh", "tools/clean-for-build.sh", variant.git_branch(), ";",
        ]
        + [RUN_VERI_PATH] + variant.run_veri_params() + ["output=../"+variant.outfile()]
        )
    print(cmd)
    return Command(str(variant), cmd)

def main():
    set_logfile(suite.logpath())
    #log("PLOT tools/aws/pull-results.py && %s && eog %s" % (suite.plot_command(), suite.png_filename()))
    log("VARIANTS %s" % suite.variants)

    workers = retrieve_running_workers(ssd=True)
    blacklist = [
    ]
    workers = [w for w in workers if w["Name"] not in blacklist]
    print(workers)
    worker_pipes = launch_worker_pipes(workers, len(suite.variants), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
