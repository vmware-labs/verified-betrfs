#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


ls -1 /home/ubuntu/verichecks-worker/worker-dir/shutdown && rm /home/ubuntu/verichecks-worker/worker-dir/shutdown && sudo shutdown --poweroff
