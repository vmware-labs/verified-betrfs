#!/usr/bin/python3

from automation import *
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--ssd', action='store_true', help="select ssd machines")
args = parser.parse_args()

def cmd_for_idx(idx, worker):
    return Command("kill", ssh_cmd_for_worker(worker) + ["killall", "-q", "VeribetrfsYcsb", "RocksYcsb", "make", "z3", "mono", "dafny"])

def main():
    workers = retrieve_running_workers(ssd=args.ssd)
    blacklist = [
        "veri-worker-b00", 
        "veri-worker-b01", 
        "veri-worker-b02", 
        "veri-worker-b03", 
        "veri-worker-b04", 
        "veri-worker-b05", 
    ]
    workers = [w for w in workers if w["Name"] not in blacklist]
    worker_pipes = launch_worker_pipes(workers, len(workers), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
