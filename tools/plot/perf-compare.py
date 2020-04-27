#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import sys
import operator
import bisect
from parser import Experiment
from PlotHelper import *
from TimeSeries import *

def plot_perf_compare(experiments):
    plotHelper = PlotHelper(4, scale=2)

    try: plotThroughput(plotHelper.nextAxis(depth=2), experiments)
    except: raise
    
    try: plotGrandUnifiedMemory(plotHelper.nextAxis(depth=2), experiments)
    except: raise

    plotHelper.save("compare.png")

experiments = []
for arg in sys.argv[1:]:
    nick,fn = arg.split("=")
    exp = Experiment(fn, nick)
    exp.sortedOpns = exp.sortedOpns[:-5]    # hack: truncate teardown tail of completed exp where memory all goes to 0
    experiments.append(exp)
plot_perf_compare(experiments)
