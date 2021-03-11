#! /bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


mkfs.ext4 /dev/xvde
mount /mnt/xvde
chown ubuntu:ubuntu /mnt/xvde
cgcreate -a ubuntu:ubuntu -t ubuntu:ubuntu -g memory:VeribetrfsExp
