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
                    color='#E5E5E5', linetype='solid', size=0.5),
                panel_grid_minor=element_blank(),
                panel_spacing=0.15,
                plot_background=element_rect(
                    fill=bgcolor, color=bgcolor, size=1),
                strip_background=element_rect(size=0)),
            inplace=True)

def throughput_vs_cores(machine, df, graph='compare-locks'):
    df['config'] = df['bench_name'] + [str(i) for i in df['n_replicas'].to_list()]
    bench_cat = pd.api.types.CategoricalDtype(categories=['dafny_nr'
                                                         , 'rust_nr'
                                                         , 'dafny_rwlock'
                                                         , 'shfllock'
                                                         , 'mcs'
                                                         , 'cpp_shared_mutex'
                                                         ], ordered=True)
    df['bench_name'] = df['bench_name'].astype(bench_cat)
    df = df.loc[df['n_threads'] >= 4]
    df['n_replicas'] = pd.Categorical(df.n_replicas)
    df['write_ratio'] = 100 - df['reads_pct']

    if graph == 'compare-locks':
        df = df.loc[~df['bench_name'].isin(['dafny_nr', 'rust_nr'])
                    | (df['n_replicas'] == 4)]
        aest = aes(x='n_threads',
                   y='ops_per_s',
                   color='bench_name',
                   shape='bench_name',
                   group='bench_name')
        labels = ['Dafny NR'
                 , 'Rust NR'
                 , 'Dafny RwLock'
                 , 'C++ ShflLock'
                 , 'C++ MCS Lock'
                 , 'C++ std::shared_mutex'
                 ]
        linetypes = ['solid', 'dashed', 'dotted']
    else:
        df = df.loc[df['bench_name'].isin(['dafny_nr', 'rust_nr'])]
        bench_cat = pd.api.types.CategoricalDtype(categories=['dafny_nr', 'rust_nr'], ordered=True)
        df['bench_name'] = df['bench_name'].astype(bench_cat)
        n_replicas_cat = pd.api.types.CategoricalDtype(categories=[1, 2, 4], ordered=True)
        df['n_replicas'] = df['n_replicas'].astype(n_replicas_cat)
        aest = aes(x='n_threads',
                   y='ops_per_s',
                   color='bench_name',
                   shape='bench_name',
                   linetype='n_replicas',
                   group='config')
        labels = ['Dafny NR', 'Rust NR']
        linetypes = ['dotted', 'dashed', 'solid']
    replicas_labels = ['1 System-wide Replica', '2 Replicas', '4 Replicas (One per NUMA node)']

    print(df)

    def write_ratio_labeller(s):
        return '%d%% Updates' % int(s)

    xskip = int(machine[1]/8)
    p = (
        ggplot(data=df,
                mapping=aest) +
        theme_my538() +
        coord_cartesian(ylim=(0, None), expand=False) +
        labs(y="Throughput (Mop/s)") +
        theme(legend_position='top', legend_title=element_blank()) + \
        scale_x_continuous(breaks=[1, 4] + list(range(xskip, 513, xskip)), name='# Threads') +
        scale_y_continuous(labels=lambda lst: ["{:,.0f}".format(x / 1_000_000) for x in lst]) +
        scale_color_manual([
            "#e41a1c",
            "#377eb8",
            "#4daf4a",
            "#984ea3",
            "#ff7f00",
            "#f781bf",
            "#999999",
            "#a6cee3",
            ],
            labels=labels) +
        scale_shape_manual(values=[
            'o',
            's',
            'D',
            '^',
            'v',
            '*',
            'O',
            'x',
            ],
            labels=labels) +
        scale_linetype_manual(linetypes, labels=replicas_labels, size=0.2) +
        #geom_point(size=0.1) +
        #geom_line(size=0.2) +
        #stat_summary(fun_data='mean_sdl', fun_args={'mult': 1}, geom='errorbar') +
        stat_summary(fun_ymin=np.min, fun_ymax=np.max, geom='errorbar', size=0.1) +
        stat_summary(fun_y=np.median, geom='line', size=0.2) +
        stat_summary(fun_y=np.median, geom='point', size=0.1) +
        #stat_summary(fun_y=np.median, geom='point') +
        facet_grid(["write_ratio", "."],
                    scales="free_y",
                    labeller=labeller(rows=write_ratio_labeller))
#guides(color=guide_legend(nrow=1))
    )

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

    p.save("%s-throughput-vs-cores-%s.png" % (machine[0], graph),
           dpi=300, width=PLOT_WIDTH, height=4*PLOT_HEIGHT,
           units=PLOT_SIZE_UNIT)
    p.save("%s-throughput-vs-cores-%s.pdf" % (machine[0], graph),
           dpi=300, width=PLOT_WIDTH, height=4*PLOT_HEIGHT,
           units=PLOT_SIZE_UNIT)

if __name__ == '__main__':
    warnings.filterwarnings('ignore')
    pd.set_option('display.max_rows', 500)
    pd.set_option('display.max_columns', 500)
    pd.set_option('display.width', 1000)
    pd.set_option('display.expand_frame_repr', True)

    for machine in MACHINES:
        df = pd.read_json('data.json')
        throughput_vs_cores(machine, df.copy(), 'compare-locks')
        throughput_vs_cores(machine, df.copy(), 'compare-nrs')
