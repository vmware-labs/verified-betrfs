#!/usr/bin/python3

from automation import *

def cmd_for_idx(idx, worker):
    return ssh_cmd_for_worker(worker) + ["ps", "-auxww", "|", "grep", "Ycsb", "|", "grep", "-v", "grep"]

def main():
    workers = retrieve_running_workers()
    worker_pipes = launch_worker_pipes(workers, len(workers), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
