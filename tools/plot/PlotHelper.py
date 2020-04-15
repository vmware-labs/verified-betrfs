#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import sys
import operator
import bisect


class Scale:
    def __init__(self, prefix, mult):
        self.prefix = prefix
        self.mult = float(mult)

    def __call__(self):
        return self.mult

    def __repr__(self):
        return self.prefix

Unit = Scale("", 1)
K = Scale("K", 1000)
Ki = Scale("Ki", 1024)
Mi = Scale("Mi", 1<<20)
Gi = Scale("Gi", 1<<30)

class AxisAllocator:
    def __init__(self, axes):
        self.axes = axes
        self.nextAxis = 0

    def get(self):
        ret = self.nextAxis
        self.nextAxis += 1
        return self.axes[ret]

class PlotHelper:
    def __init__(self, numPlots, scale=1):
        self.numPlots = numPlots
        columns = 2 if numPlots > 4 else 1
        rows = int((numPlots+0.5)/columns)
        self.fig, self.axes = plt.subplots(rows, columns, figsize=(scale*6*columns, scale*rows*2))
        self.axes = self.axes.transpose().flatten()
        plt.subplots_adjust(left=0.10, right=0.90, hspace=0.4, top=0.95, bottom=0.05);

        self.axisAllocator = AxisAllocator(self.axes)

    def nextAxis(self):
        return self.axisAllocator.get()

    def save(self, figname):
        plt.tight_layout()
        plt.savefig(figname)
