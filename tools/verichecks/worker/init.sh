#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


rm /root/verichecks-worker/worker-dir/shutdown || true
rm -Rf /root/verichecks-worker/worker-dir/clones/*
cd /root/verichecks-worker
. ./venv3/bin/activate
python3 run.py || true
touch /root/verichecks-worker/worker-dir/shutdown
exec /bin/bash
