#!/usr/bin/python3

import subprocess
from automation import *

def launch_worker_pipes(workers):
    worker_pipes = []
    for workeri in range(len(workers)):
        worker = workers[workeri]

        cmd = ssh_cmd_for_worker(worker) + ["killall", "VeribetrfsYcsb", ";", "killall", "RocksYcsb"]
        print("launching worker %d on %s: %s" % (workeri, worker["Name"], " ".join(cmd)))
        worker_pipe = subprocess.Popen(cmd)
        worker_pipes.append(worker_pipe)
    return worker_pipes

def main():
    workers = retrieve_running_workers()
    worker_pipes = launch_worker_pipes(workers)
    monitor_worker_pipes(worker_pipes)
    print("All jobs complete.")

main()
