#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Feb 11 15:05:24 2020

@author: michael
"""

import json
from numpy import mean
import numpy as np
import re
import math
import os
from itertools import takewhile, dropwhile
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib import gridspec
import pickle
from scipy.stats import mannwhitneyu
from matplotlib import rc, rcParams
rc('text', usetex=True)

rcParams.update(
    {   
    "text.usetex": True,                
    "font.family": "sans-serif",
    "text.latex.preamble" : r"\usepackage{cmbright}\usepackage[notmath]{sansmathfonts}"
    }
)

runtime_re = re.compile("Completed in (\d+)h (\d+)m (\d+).\d+s")

homedir = "/home/michael/Documents/efsm-inference/inference-tool/results"
# homedir = "/home/michael/Documents/results"

data = {
    "liftDoors": {},
    "spaceInvaders": {},
    "drinks": {},
    "spaceInvadersGuards": {}
    }

systems = ["drinks", "spaceInvadersGuards"]
systems = ["liftDoors", "spaceInvaders"]


def configs(p):
    if p == "liftDoors":
        return [
            # 'pta',
            # 'none',
            'MINT',
            'gp',
            # 'obfuscated-time-none',
            'obfuscated-time-gp'
            ]
    if p == "spaceInvaders":
        return [
            # 'pta',
            # 'none',
            'MINT',
            'gp',
            # 'obfuscated-aliens-none',
            'obfuscated-aliens-gp',
            # 'obfuscated-shields-none',
            'obfuscated-shields-gp',
            # 'obfuscated-x-none',
            'obfuscated-x-gp',
            # Extras
            'obfuscated-aliens-x-gp',
            'obfuscated-x-shields-gp',
            'obfuscated-aliens-shields-gp'
            ]
    if p == "drinks" or p == "spaceInvadersGuards":
        return [
            'pta',
            'none',
            'gp',
            'gp-distinguish'
            ]
    return sorted(list(data[p].keys()))


def axesColour(ax):
    ax.spines['bottom'].set_color('#dddddd')
    ax.spines['top'].set_color('#dddddd') 
    ax.spines['right'].set_color('#dddddd')
    ax.spines['left'].set_color('#dddddd')
    ax.tick_params(axis='x', color='#dddddd')
    ax.tick_params(axis='y', color='#dddddd')


def box1(column, program, cfgs, fname, title, ax1):
    print(program, data[program].keys())
    cfgs = [c for c in cfgs if c in data[program]]
    if column == 'runtime':
        cfgs = [c for c in cfgs if c != 'pta']
    
    if column == 't1' or column == "prop":
        boxes_aux = [data[program][config][column] for config in cfgs]
        boxes = [[item for sublist in l for item in sublist] for l in boxes_aux]
    else:
        boxes = [data[program][config][column].astype(float) for config in cfgs]
    
    ax1.boxplot(
            boxes,
            widths=0.4
          )

    labels = [" ".join(c.replace("obfuscated", "obfuscated\n").replace("pta", "PTA").replace("none", "without\npreprocessing").replace("distinguish", "\nguards").replace("gp", "GP").split("-")) for c in cfgs]
    # ax1.set_xticks(range(0, len(labels)+1))
    ax1.set_xticklabels(
        labels,
        rotation=30,
        ha='right',
        va='top',
        ma='right',
        rotation_mode="anchor"
    )
    ax1.tick_params(axis='both', labelsize=10)

    axesColour(ax1)
    ax1.set_title(title)
    ax1.margins()
    return boxes
    
def boxPlots(column, ps, fname, systems):
    size = 0
    for p in systems:
        for c in ps[p]:
            size += 1
    
    # fig1 = plt.figure(figsize=(0.8*size, 3))
    # spec = gridspec.GridSpec(nrows=1, ncols=len(systems), width_ratios=[len(ps[p]) for p in systems])

    fig, axs = plt.subplots(
        nrows=1,
        ncols=len(systems),
        sharex='col',
        sharey='row',
        figsize=(0.8*size, 2.5),
        gridspec_kw={'width_ratios': [len(ps[p]) for p in systems]}
        )
    # plt.subplots_adjust(wspace=0.08)
    
    print(f"box {fname}-{column} size: {size}")
    
    title = (
        "Accepted Prefix" if column == "t1" else 
        "NRMSE" if column == "nrmse" else 
        "Runtime (Minutes)" if column == "runtime" else
        column.capitalize()
        )
    
    boxes = []
    for i, p in enumerate(systems):
        ax = axs[i]
        ax.yaxis.set_tick_params(which='both', labelleft=True)

        cfgs = configs(p)
        
        b = box1(column, p, cfgs, fname, r"\textsc{"+p+"} "+title, ax)
        boxes.append(b)


    # plt.tight_layout()
    plt.savefig(f"{homedir}/graphs/{fname}.pdf", bbox_inches='tight')
    plt.close()
    print("Saving to", f"{homedir}/graphs/{fname}.pdf",)
    return boxes


if not os.path.exists(f"{homedir}/graphs"):
    os.mkdir(f"{homedir}/graphs")


# Load in the data from pickle if we can so we don't have to keep recalculating stuff
with open(f'{homedir}/data.dic', 'rb') as f:
    data = pickle.load(f)

fname = "".join([p[:2] for p in systems])

ps = {p:configs(p) for p in data}

ls, ss = boxPlots("sensitivity", ps, f"{fname}-sensitivity-plots", systems)
lt, st = boxPlots("t1", ps, f"{fname}-t1-plots", systems)
lt, st = boxPlots("states", ps, f"{fname}-states-plots", systems)
lt, st = boxPlots("transitions", ps, f"{fname}-transitions-plots", systems)
lt, st = boxPlots("runtime", ps, f"{fname}-runtime-plots", systems)


cfgs = ["pta", "none", "gp", "MINT"]



fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(
        nrows=2,
        ncols=2,
        figsize=(0.9*11, 6),
        gridspec_kw={'width_ratios': [3, 8], "wspace":0.12, "hspace":0.2}
        )

ax1.boxplot(ls, widths=0.4)
ax1.title.set_text(r"\textsc{"+"liftDoors} "+' Sensitivity')
ax2.boxplot(ss, widths=0.4)
ax2.title.set_text(r"\textsc{"+"spaceInvaders} "+' Sensitivity')

ax3.boxplot(lt, widths=0.4)
ax3.title.set_text(r"\textsc{"+"liftDoors} "+' Accepted Prefix')
ax3.set_xticklabels(
    [" ".join(c.replace("obfuscated", "obfuscated\n").replace("pta", "PTA").replace("none", "without\npreprocessing").replace("distinguish", "\nguards").replace("gp", "GP").split("-")) for c in configs("liftDoors")],
    rotation=30,
    ha='right',
    va='top',
    ma='right',
    rotation_mode="anchor"
)

ax4.boxplot(st, widths=0.4)
ax4.title.set_text(r"\textsc{"+"spaceInvaders} "+' Accepted Prefix')
ax4.set_xticklabels(
    [" ".join(c.replace("obfuscated", "obfuscated\n").replace("pta", "PTA").replace("none", "without\npreprocessing").replace("distinguish", "\nguards").replace("gp", "GP").split("-")) for c in configs("spaceInvaders")],
    rotation=30,
    ha='right',
    va='top',
    ma='right',
    rotation_mode="anchor"
)

ax1.xaxis.set_tick_params(which='major', labelleft=False)
ax2.xaxis.set_tick_params(which='major', labelleft=False)

for ax in fig.get_axes():
    ax.yaxis.set_tick_params(which='both', labelleft=True)
    ax.margins()
    axesColour(ax)

# plt.savefig("/home/michael/Documents/papers/gp-paper/figures/graphs/lisp-plots.pdf", bbox_inches='tight')
