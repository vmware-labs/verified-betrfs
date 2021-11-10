#!/usr/bin/env python3

import sys
import os
import os.path
import glob
import subprocess
import random

NUMA_POLICY = 'interleave'
SECONDS = 30

CORES_PER_NODE = 48
NODES = 4
MAX_THREADS = NODES * CORES_PER_NODE

BENCHES = ['dafny_nr', 'dafny_rwlock', 'cpp_shared_mutex']

N_THREADS = [1] + list(range(4, MAX_THREADS, 4))

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
    subprocess.run(cmd, shell=True, check=False)

def run_all():
    threads = N_THREADS[1:-1]
    random.shuffle(threads)
    threads = [N_THREADS[-1]] + threads + [N_THREADS[0]]
    print(threads)
    for n_threads in threads:
        for n_replicas in [1, 2, 4]:
            bench = 'dafny_nr'
            assert bench == BENCHES[0]
            if (n_threads < n_replicas):
                continue
            run(bench, n_replicas, n_threads)
            combine_data_files()

        for bench in BENCHES[1:]:
            run(bench, 1, n_threads)
            combine_data_files()

if __name__ == '__main__': run_all()
