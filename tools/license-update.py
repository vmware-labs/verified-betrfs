#!/usr/bin/env python3
# Replace/insert license headers.
# Usage:
# cd Splinter/; find . -name \*.rs | xargs ../tools/license-update.py

import sys

expected_license = """\
// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
"""

def check(path):
    lines = open(path).readlines()
    found = "".join(lines[0:2])
    if found == expected_license:
        rc = "YAY"
    else:
        if "Copyright" in found:
            rc = "NEEDSFIX"
            newfile = expected_license + "".join(lines[2:])
        else:
            rc = "BOO"
            newfile = expected_license + "".join(lines)
        open(path, "w").write(newfile)
    print(path, rc)

for path in sys.argv[1:]:
    check(path)

