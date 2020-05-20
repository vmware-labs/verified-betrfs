#!/usr/bin/python3
import sys
import os
sys.path.append(os.path.dirname(__file__)+"/..")

import re
from automation import *
from suite import *
from lib_deps import *

ROOT="Impl/Bundle.i.dfy"
#ROOT="lib/DataStructures/MutableBtree.i.dfy"   # a small test case
SUITE_NAME="veri_time_09"

def constructSuite(nReplicas):
    values = []
    for source in depsFromDfySources([ROOT]):
        clean_path = re.sub("[^A-Za-z0-9-]", "_", source.normPath)
        values.append(Value(clean_path, source.normPath))
    sourceVariable = Variable("source", "source", values)
    replicaVariable = Variable("replica", "silent", [Value("r%d"%i, "r%d"%i) for i in range(nReplicas)])
    suite = Suite(SUITE_NAME, sourceVariable, replicaVariable)
    return suite

RUN_VERI_PATH="tools/run-veri-config-experiment.py"

def main():
    def cmd_for_idx(idx, worker):
        variant = suite.variants[idx]
        source_path = variant.value_by_name("source").param_value
        output_path = "../" + variant.outfile()
        cmd = (ssh_cmd_for_worker(worker) + [
            "cd", "veribetrfs", ";",
            "echo", "WORKER", worker["Name"], ">", output_path, ";",
    #        "sleep", "1",
            "tools/local-dafny.sh", source_path, "/compile:0", "/trace", ">>", output_path
            ]
            )
        return Command(str(variant), cmd)

    suite = constructSuite(2)
    set_logfile(suite.logpath())
    log("VARIANTS %s" % suite.variants)

    workers = retrieve_running_workers()
    sequenced_launcher(workers, len(suite.variants), cmd_for_idx, dry_run=False)

main()
