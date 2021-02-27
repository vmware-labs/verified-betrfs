#! /bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT


DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
$DIR/../.dafny/bin/dafny "$@"
