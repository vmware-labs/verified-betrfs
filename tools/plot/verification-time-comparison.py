#!/usr/bin/python3
import sys
import os
sys.path.append(os.path.dirname(__file__)+"/..")
sys.path.append(os.path.dirname(__file__)+"/../aws")

import re
from automation import *
from suite import *
from lib_deps import *

ROOT="Impl/IndirectionTableImpl.i.dfy"

paths = set()
for source in depsFromDfySources([ROOT]):
    # depsFromDfySources seems to produce some duplication; not sure why
    paths.add(source.normPath)

values = []
for path in paths:
    clean_path = re.sub("[^A-Za-z0-9-]", "_", path)
    values.append((clean_path, path))

print(values)


