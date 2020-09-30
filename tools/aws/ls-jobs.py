#!/usr/bin/python3

from automation import *

parser = argparse.ArgumentParser(parents=[automation_argparser])
args = parser.parse_args()

def cmd_for_idx(idx, worker):
    return Command("ls", ssh_cmd_for_worker(worker) + ["ps", "-auxww", "|", "grep", "Ycsb", "|", "grep", "-v", "grep"])

def main():
    workers = retrieve_running_workers(workers_file=args.workers_file, ssd=args.ssd)
    worker_pipes = launch_worker_pipes(workers, len(workers), cmd_for_idx, dry_run=args.dry_run)
    monitor_worker_pipes(worker_pipes)

main()
