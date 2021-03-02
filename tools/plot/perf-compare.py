#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import sys
import operator
import bisect
from parser import Experiment
from PlotHelper import *
from TimeSeries import *

output_filename = "compare.png"

def plot_perf_compare(experiments):
    plotHelper = PlotHelper(4, scale=2)

    try: plotThroughput(plotHelper.nextAxis(depth=2), experiments)
    except: raise
    
    try: plotGrandUnifiedMemory(plotHelper.nextAxis(depth=2), experiments)
    except: raise

#    try: plotSlowIos(plotHelper.nextAxis(depth=2), experiments)
#    except: pass
#
#    try: plotCpuTime(plotHelper.nextAxis(depth=2), experiments)
#    except: raise
#
#    try: plotProcIoBytes(plotHelper.nextAxis(depth=2), experiments)
#    except: raise

#    try: plotIoLatencyCdf(plotHelper.nextAxis(depth=2), experiments)
#    except: raise

#    try: plotRocksIo(plotHelper.nextAxis(depth=2), experiments)
#    except: raise

    plotHelper.save(output_filename)

experiments = []
for arg in sys.argv[1:]:
    nick,fn = arg.split("=")
    if nick=="output":
        output_filename = fn
    else:
        try:
            exp = Experiment(fn, nick)
            #exp.sortedOpns = exp.sortedOpns[:-5]    # hack: truncate teardown tail of completed exp where memory all goes to 0
            experiments.append(exp)
        except (ValueError,FileNotFoundError):
            print("Can't parse %s; skipping" % nick)
plot_perf_compare(experiments)
