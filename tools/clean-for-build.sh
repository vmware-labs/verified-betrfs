#!/bin/sh

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

# Args: git-branch to check out
git fetch
git checkout $*
git pull
git rev-parse --abbrev-ref HEAD
tools/update-submodules.sh
tools/update-dafny.sh
rm -rf build/
make clean
