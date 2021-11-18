#!/usr/bin/env python3

import sys
import os
import os.path
import glob
import subprocess
import random
import time

NUMA_POLICY = 'interleave'
SECONDS = 30

CORES_PER_NODE = 48
NODES = 4
MAX_THREADS = NODES * CORES_PER_NODE

NR_BENCHES = ['dafny_nr', 'rust_nr']
OTHER_BENCHES = ['dafny_rwlock', 'shfllock', 'mcs', 'cpp_shared_mutex']
READS_PCT = [100, 95, 50, 0, 90]

N_REPLICAS = [1, 2, 4]

ITERS = 1

def reorder(l):
  if len(l) < 2:
    return l
  p = len(l) // 2
  return [l[p]] + reorder(l[p+1:] + l[:p])
N_THREADS = [MAX_THREADS, 4] + reorder(list(range(16, MAX_THREADS, 16)))

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

def run(bench, n_replicas, n_threads, reads_pct, run_id_num):
    path = bench_path(n_replicas)
    cmd = '%s %s %d %d %d %s %s' % (path, bench, n_threads, reads_pct,
                                   SECONDS, NUMA_POLICY, run_id_num)
    print(cmd)
    subprocess.run(cmd, shell=True, check=False)

def run_all():
    subprocess.run('rm data*.json *throughput*.pdf *throughput*.png', shell=True, check=False)

    try:
        os.mkdir('runs')
    except:
        pass

    run_id = time.strftime('run%Y%m%d%H%M%S')
    try:
        os.mkdir(os.path.join('runs', run_id))
    except:
        pass

    run_num = -1
    for i in range(ITERS):
        run_num += 1
        run_id_num = run_id + '-' + str(run_num)
        for reads_pct in READS_PCT:
            for n_threads in N_THREADS:
                for n_replicas in N_REPLICAS:
                    for bench in NR_BENCHES:
                      if (n_threads < n_replicas):
                          continue
                      run(bench, n_replicas, n_threads, reads_pct, run_id_num)

                for bench in OTHER_BENCHES:
                    run(bench, 1, n_threads, reads_pct, run_id_num)

                combine_data_files()
                subprocess.run('./plot.py', shell=True, check=False)
                subprocess.run('cp *.json *.png *.pdf runs/%s' % run_id, shell=True, check=False)

if __name__ == '__main__': run_all()
