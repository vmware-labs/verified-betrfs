#!/usr/bin/python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause


import subprocess
from automation import *
import argparse

parser = argparse.ArgumentParser(parents=[automation_argparser])
args = parser.parse_args()

def cmd_for_idx(idx, worker):
    return Command("pull", ["rsync", "-zrav", "-e", " ".join(ssh_preamble()), ssh_target_for_worker(worker)+":expresults/", "expresults/"])

def main():
    workers = retrieve_running_workers(workers_file=args.workers_file, ssd=args.ssd)
    worker_pipes = launch_worker_pipes(workers, len(workers), cmd_for_idx, dry_run=args.dry_run)
    monitor_worker_pipes(worker_pipes)

main()
