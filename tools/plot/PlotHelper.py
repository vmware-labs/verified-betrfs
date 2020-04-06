#!/usr/bin/env python3
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import sys
import operator
import bisect

Kilo = 1000
MB = float(1<<20)
GB = float(1<<30)

class AxisAllocator:
    def __init__(self, axes):
        self.axes = axes
        self.nextAxis = 0

    def get(self):
        ret = self.nextAxis
        self.nextAxis += 1
        return self.axes[ret]

class PlotHelper:
    def __init__(self, numPlots):
        self.numPlots = numPlots
        columns = 2 if numPlots > 4 else 1
        rows = int((numPlots+1)/columns)
        self.fig, self.axes = plt.subplots(rows, columns, figsize=(6*columns,rows*2))
        self.axes = self.axes.transpose().flatten()
        plt.subplots_adjust(left=0.10, right=0.90, hspace=0.4, top=0.95, bottom=0.05);

        self.axisAllocator = AxisAllocator(self.axes)

    def nextAxis(self):
        return self.axisAllocator.get()

    def save(self, figname):
        plt.tight_layout()
        plt.savefig(figname)
