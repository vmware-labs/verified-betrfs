#!/bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause


set -e
set -x

USER=`id -u -n`
GROUP=`id -g -n`

sudo cgcreate -a $USER:$GROUP -t $USER:$GROUP -g memory:VeribetrfsExp
