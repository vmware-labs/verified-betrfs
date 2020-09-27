#!/usr/bin/python3
import sys
import os
sys.path.append(os.path.dirname(__file__)+"/..")

import re
from automation import *
from suite import *
from lib_deps import *

# Consider updating all the workers before running the experiment!
# tools/aws/run-all.py "cd veribetrfs; git checkout master; git pull"
# tools/aws/run-all.py "cd veribetrfs; tools/update-submodules.sh; tools/update-dafny.sh"
ROOT="Impl/Bundle.i.dfy"
#ROOT="lib/DataStructures/MutableBtree.i.dfy"   # a small test case
SUITE_NAME="veri_time_september_02"   # one big parallel build
N_REPLICAS=5

def listSources():
    paths = set()
    for source in depsFromDfySources([ROOT]):
        # depsFromDfySources seems to produce some duplication; not sure why
        paths.add(source.normPath)

    values = []
    for path in paths:
        clean_path = re.sub("[^A-Za-z0-9-]", "_", path)
        values.append(Value(clean_path, path))
    return values

def constructSuite(nReplicas):
    sourceVariable = Variable("source", "source", listSources()[::-1])
    replicaVariable = Variable("replica", "silent", [Value("r%d"%i, "r%d"%i) for i in range(nReplicas)])
    branchVariable = Variable("git_branch", "git_branch", [
        Value("dynamic-frames", "osdi20-artifact-dynamic-frames-vertime"),
        ])
    suite = Suite(SUITE_NAME, sourceVariable, replicaVariable, branchVariable)
    return suite

RUN_VERI_PATH="tools/run-veri-config-experiment.py"

def main():
    def cmd_for_idx(idx, worker):
        variant = suite.variants[idx]
        source_path = variant.value_by_name("source").param_value
        output_path = "../" + variant.outfile()
        cmd = (ssh_cmd_for_worker(worker) + [
            "cd", "veribetrfs", ";",
            "sh", "tools/clean-for-build.sh", variant.git_branch(), ";",
            "echo", "WORKER", worker["Name"], ">", output_path, ";",
    #        "sleep", "1",
            "tools/local-dafny.sh", source_path, "/compile:0", "/trace", ">>", output_path
#            "tools/local-dafny.sh", source_path, "/compile:0", "/trace", "/noNLarith", ">>", output_path
            ]
            )
        return Command(str(variant), cmd)

    suite = constructSuite(N_REPLICAS)
    set_logfile(suite.logpath())
    #log("VARIANTS %s" % suite.variants)

    for variant in suite.variants:
        log("VARIANT %s" % variant)
    log("NUM_SOURCES %s" % len(listSources()))
    log("NUM_VARIANTS %s" % len(suite.variants))

    workers = retrieve_running_workers(ssd=False)
    sequenced_launcher(workers, len(suite.variants), cmd_for_idx, dry_run=False)

main()
