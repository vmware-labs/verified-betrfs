#!/usr/bin/python3

import subprocess
from automation import *

def cmd_for_idx(idx, worker):
    return Command("pull", ["rsync", "-zrav", "-e", " ".join(ssh_preamble()), ssh_target_for_worker(worker)+":expresults/", "expresults/"])

def main():
    workers = retrieve_running_workers("ssd")
    worker_pipes = launch_worker_pipes(workers, len(workers), cmd_for_idx, dry_run=False)
    monitor_worker_pipes(worker_pipes)

main()
