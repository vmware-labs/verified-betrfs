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
    plotHelper = PlotHelper(2, scale=2)

    for e in experiments:
        e.nickname = e.filename.split("/")[-1]


    try:
        plotThroughput(plotHelper.nextAxis(depth=2), experiments)
    except: raise
        

    plotHelper.save("compare.png")

experiments = [Experiment(fn) for fn in sys.argv[1:]]
plot_perf_compare(experiments)
