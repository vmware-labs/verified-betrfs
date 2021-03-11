# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import sys
import re

try:
    file = open(sys.argv[1])
except:
    sys.exit(0)

re_datatype = re.compile("^(linear )?datatype ([A-Za-z0-9_]+)")
re_type = re.compile("^type ([A-Za-z0-9_]+)")
re_function = re.compile("^function( method)?( \{.+\})? ([A-Za-z0-9_]+)")
re_predicate = re.compile("^predicate( method)?( \{.+\})? ([A-Za-z0-9_]+)")
re_lemma = re.compile("^lemma ([A-Za-z0-9_]+)")
re_protected = re.compile("^protected (function|predicate) ([A-Za-z0-9_]+)")

exports = set()

for line in file:
    line = line.strip()

    if ":opaque" in line:
        continue

    match = re.match(re_datatype, line)

    if match:
        exports.add(match.group(2))
        # print(match.group(1))
        continue
    
    match = re.match(re_type, line)
    if match:
        exports.add(match.group(1))
        # print(match.group(1))
        continue

    match = re.match(re_function, line)

    if match:
        exports.add(match.group(3))
        # print(match.group(3))
        continue

    match = re.match(re_predicate, line)
    if match:
        exports.add(match.group(3))
        continue

    # match = re.match(re_lemma, line)
    # if match:
    #     exports.add(match.group(1))
    #     # print(match.group(1))
    #     continue

    # match = re.match(re_protected, line)
    # if match:
    #     print(match.group(2))
    #     continue

exports = """
// begin generated export
  export Spec
    provides *
    reveals %s
  export extends Spec
// end generated export
    """ % (", ".join(exports))

print(exports)