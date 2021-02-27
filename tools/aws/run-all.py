#!/usr/bin/python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause


import sys
from automation import *
import argparse

parser = argparse.ArgumentParser(parents=[automation_argparser])
parser.add_argument('command')
args = parser.parse_args()

def cmd_for_idx(idx, worker):
    return Command("run", ssh_cmd_for_worker(worker) + [args.command])

def main():
    workers = retrieve_running_workers(workers_file=args.workers_file, ssd=args.ssd)
    worker_pipes = launch_worker_pipes(workers, len(workers), cmd_for_idx, dry_run=args.dry_run)
    monitor_worker_pipes(worker_pipes)

main()
