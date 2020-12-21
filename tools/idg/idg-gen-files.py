#!/usr/bin/python3
"""
This file is meant to be run from BlockCacheSystem/ and it will generate many files for the IDG experiments

Example run:
python3 ../tools/idg/idg-gen-files.py

"""

lines = open('BlockSystem.i.dfy').read().splitlines()

i_pre = 511
i_post = 547

assert '    && Inv1(s)' == lines[i_pre]
assert '    && Inv1(s)' == lines[i_post]

if False:
    for i in range(32):
        lines_i = lines[:]
        lines_i[i_pre + i] = '// ' + lines_i[i_pre + i]
        lines_i[i_post + i] = '// ' + lines_i[i_post + i]
        fn = f'BlockSystem.{i}.i.dfy'
        open(fn, 'w').write('\n'.join(lines_i))

if False:
    for j in range(32):
        lines_ = lines[:]
        lines_[i_pre + j] = '// ' + lines_[i_pre + j]
        for k in range(32):
            lines_[i_post + k] = '// ' + lines_[i_post + k]
        fn = f'BlockSystem.none.{j}.i.dfy'
        open(fn, 'w').write('\n'.join(lines_))

if True:
    needed = set([0, 1, 2, 3, 6, 7, 9, 10, 11, 14, 15, 16, 17, 19, 20, 28, 29, 30, 31])
    for i in range(32):
        for j in range(32):
            if i == j or j in needed:
                continue
            lines_ = lines[:]
            lines_[i_pre + j] = '// ' + lines_[i_pre + j]
            for k in range(32):
                if k != i:
                    lines_[i_post + k] = '// ' + lines_[i_post + k]
            fn = f'BlockSystem.{i}.{j}.i.dfy'
            open(fn, 'w').write('\n'.join(lines_))
