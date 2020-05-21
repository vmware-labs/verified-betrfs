#!/usr/bin/python3

from automation import *

def cmd_for_idx(idx, worker):
    return Command("kill", ssh_cmd_for_worker(worker) + ["killall", "-q", "VeribetrfsYcsb", "RocksYcsb", "make", "z3", "mono", "dafny"])

def main():
    workers = retrieve_running_workers()
    worker_pipes = launch_worker_pipes(workers, len(workers), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
