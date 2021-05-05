#!/bin/bash

# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause


if [ x$1 == "x-d" ]; then
    DRY_RUN=-d
fi

./tools/copywriter.sh $DRY_RUN `find -type f | grep -v ./lib/Marshalling/ | grep -v ./lib/Math/ | grep -v ./vendor/ | grep -v ./.git/ | grep -v ./.dafny/`
