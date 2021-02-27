#!/bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT


g++ -o tools/clear-os-page-cache tools/clear-os-page-cache.cpp

echo "requesting sudo access to give tools/clear-os-page-cache script root privileges"
sudo tools/set-privileges-on-script.sh
echo "done"
