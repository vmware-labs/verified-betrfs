#!/bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT


# To free pagecache:
# echo 1 > /proc/sys/vm/drop_caches
#
# To free dentries and inodes:
# echo 2 > /proc/sys/vm/drop_caches
#
# To free pagecache, dentries and inodes:
# echo 3 > /proc/sys/vm/drop_caches

echo 3 > /proc/sys/vm/drop_caches
