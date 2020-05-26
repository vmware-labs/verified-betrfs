#!/usr/bin/python3

import sys
from automation import *

def cmd_for_idx(idx, worker):
    return Command("run", ssh_cmd_for_worker(worker) + sys.argv[1:])

def main():
    workers = retrieve_running_workers(ssd=True)
    blacklist = []
    # blacklist = [
    # ]
    workers = [w for w in workers if w["Name"] not in blacklist]
    worker_pipes = launch_worker_pipes(workers, len(workers), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
