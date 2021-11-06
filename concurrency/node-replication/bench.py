#!/usr/bin/env python3

import sys
import os
import os.path
import glob
import subprocess

NUMA_POLICY = 'interleave'
SECONDS = 10

CORES_PER_NODE = 48
NODES = 2
MAX_THREADS = NODES * CORES_PER_NODE

BENCHES = ['dafny_nr', 'dafny_rwlock', 'cpp_shared_mutex']
ALLOWED_N_REPLICAS = [1, 2, 4]

def bench_path(n_replicas):
    p = './app-%dreplicas' % n_replicas
    os.path.isfile(p) and os.access(p, os.X_OK)
    return p

def combine_data_files():
    filepaths = glob.glob('data-*.json')

    json_records = []
    for filepath in filepaths:
        with open(filepath) as f:
            json_records.append(f.read())

    combined_json = '[\n' + ',\n'.join(json_records) + '\n]'

    with open('data.json', 'w') as f:
        f.write(combined_json)

def run(bench, n_replicas, n_threads):
    path = bench_path(n_replicas)
    cmd = '%s %s %d %d %s' % (path, bench, n_threads,
                                   SECONDS, NUMA_POLICY)
    print(cmd)
    subprocess.run(cmd, shell=True, check=True)

def run_all():
    for n_replicas in [1, 2, 4]:
        for bench in BENCHES:
            for n_threads in [1] + list(range(4, MAX_THREADS, 4)):
                if n_threads < n_replicas:
                    continue
                run(bench, n_replicas, n_threads)
                combine_data_files()

if __name__ == '__main__': run_all()