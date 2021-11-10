#!/usr/bin/env python3

from plotnine.themes.theme_gray import theme_gray
from plotnine.themes.theme import theme
from plotnine.themes.elements import (element_line, element_rect,
                                      element_text, element_blank)
import sys
import pandas as pd
import numpy as np
import plotnine as p9

from plotnine import *
from plotnine.data import *

import warnings

from io import BytesIO

# this is the width of a column in the latex template
LATEX_TEMPLATE_COLUMNWIDTH = 84.70798

# the unit of the latex template column width
LATEX_TEMPLATE_COLUMNWDITH_UNIT = 'mm'

# this is the width of the plot
PLOT_WIDTH = LATEX_TEMPLATE_COLUMNWIDTH

# this is the size unit
PLOT_SIZE_UNIT = LATEX_TEMPLATE_COLUMNWDITH_UNIT

# this is the ration of the plot
PLOT_ASPECT_RATIO = 16/6

# this is the plot height
PLOT_HEIGHT = PLOT_WIDTH/PLOT_ASPECT_RATIO

# What machine, max cores, sockets, revision
MACHINES = [('skylake4x', 192, 4, '4b3c410')]


# MACHINES = [('skylake8x', 448)]
# REVISION = '3e08eac617'

# Us the best obtained results for each DT
BENCHMARKS = {
    'hashmap': ("Socket", "Interleave", "128"),
    'chashmap': ("One", "Interleave", "128"),
    'std': ("One", "Interleave", "128"),
    'flurry': ("One", "Interleave", "128"),
    'urcu': ("One", "Interleave", "128"),
    'dashmap': ("One", "Interleave", "128"),
}

class theme_my538(theme_gray):
    def __init__(self, base_size=6, base_family='DejaVu Sans'):
        theme_gray.__init__(self, base_size, base_family)
        bgcolor = '#FFFFFF'
        self.add_theme(
            theme(
                strip_margin=0,
                strip_margin_x=0,
                strip_margin_y=0,
                legend_box_margin=0,
                legend_margin=0,
                axis_text=element_text(size=base_size),
                axis_ticks=element_blank(),
                title=element_text(color='#3C3C3C'),
                legend_background=element_rect(fill='None'),
                legend_key=element_rect(fill='#FFFFFF', colour=None),
                panel_background=element_rect(fill=bgcolor),
                panel_border=element_blank(),
                panel_grid_major=element_line(
                    color='#D5D5D5', linetype='solid', size=0.5),
                panel_grid_minor=element_blank(),
                panel_spacing=0.15,
                plot_background=element_rect(
                    fill=bgcolor, color=bgcolor, size=1),
                strip_background=element_rect(size=0)),
            inplace=True)

def throughput_vs_cores(machine, df, write_ratios=[0, 10, 80]):
    df['config'] = df['bench_name'] + [str(i) for i in df['n_replicas'].to_list()]
    df = df.loc[df['n_threads'] >= 4]
    df['n_replicas'] = pd.Categorical(df.n_replicas)
    xskip = int(machine[1]/8)
    p = ggplot(data=df,
               mapping=aes(x='n_threads',
                           y='ops_per_s',
                           color='config',
                           shape='config',
                           group='config')) + \
        theme_my538() + \
        coord_cartesian(ylim=(0, None), expand=False) + \
        labs(y="Throughput [Melems/s]") + \
        theme(legend_position='top', legend_title=element_blank()) + \
        scale_x_continuous(breaks=[1, 4] + list(range(xskip, 513, xskip)), name='# Threads') + \
        scale_y_continuous(labels=lambda lst: ["{:,.0f}".format(x / 1_000_000) for x in lst]) + \
        scale_color_manual([
            "#e41a1c",
            "#377eb8",
            "#4daf4a",
            "#984ea3",
            "#ff7f00",
            "#f781bf",
            "#999999",
            "#a6cee3",
            ]) + \
        scale_shape_manual(values=[
            'o',
            's',
            'D',
            '^',
            'v',
            '*',
            ]) + \
        geom_point() + \
        geom_line() + \
        facet_grid(["reads_pct", "."], scales="free_y") + \
        guides(color=guide_legend(nrow=1))
#        scale_color_manual([
#            "#66C2A5",
#            "#8DA0CB",
#            "#E78AC3",
#            "#FC8D62",
#            "#A6D854",
#            "#FFD92F",
#            "#E5C494",
#            "#B3B3B3",
#            ]) + \

    #sockets = machine[2]
    #threads_per_socket = machine[1] / machine[2]
    #annotation_data = []
    #for wr in benchmarks['write_ratio'].unique():
    #    ht = 0
    #    for hts in range(0, 2):
    #        for s in range(0, sockets):
    #            ht += threads_per_socket / 2
    #            lt = ('B', 'A')[ht == machine[1] / 2]
    #            annotation_data.append(
    #                [wr, ht, max(benchmarks.loc[benchmarks['write_ratio'] == wr]['throughput']), lt])

    #annotations = pd.DataFrame(annotation_data, columns=[
    #                           'write_ratio', 'threads', 'yend', 'lt'])
    #p += geom_segment(data=annotations,
    #                  mapping=aes(x='threads', xend='threads',
    #                              y=0, yend='yend', linetype='lt'),
    #                  color='black')
    #p += scale_linetype_manual(values=['dashed', 'dotted'],
    #                           guide=None)

    p.save("{}-throughput-vs-cores.png".format(machine[0]),
           dpi=300, width=PLOT_WIDTH, height=PLOT_HEIGHT,
           units=PLOT_SIZE_UNIT)
    p.save("{}-throughput-vs-cores.pdf".format(machine[0]),
           dpi=300, width=PLOT_WIDTH, height=PLOT_HEIGHT,
           units=PLOT_SIZE_UNIT)

if __name__ == '__main__':
    warnings.filterwarnings('ignore')
    pd.set_option('display.max_rows', 500)
    pd.set_option('display.max_columns', 500)
    pd.set_option('display.width', 1000)
    pd.set_option('display.expand_frame_repr', True)

    for machine in MACHINES:
        df = pd.read_json('data.json')
        print(df)
        throughput_vs_cores(machine, df)
