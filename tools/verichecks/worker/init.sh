#! /bin/bash

rm /root/verichecks-worker/worker-dir/shutdown || true
rm -Rf /root/verichecks-worker/worker-dir/clones/*
cd /root/verichecks-worker
. ./venv3/bin/activate
python3 run.py || true
touch /root/verichecks-worker/worker-dir/shutdown
exec /bin/bash
