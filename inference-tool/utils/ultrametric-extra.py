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
    "spaceInvaders": {},
    }

systems = ["liftDoors", "spaceInvaders"]


def configs(p):
    if p == "spaceInvaders":
        return [
            'pta',
            'obfuscated-aliens-x-gp',
            'obfuscated-aliens-shields-gp',
            'obfuscated-x-shields-gp'
            ]
    return sorted(list(data[p].keys()))


def axesColour(ax):
    ax.spines['bottom'].set_color('#dddddd')
    ax.spines['top'].set_color('#dddddd') 
    ax.spines['right'].set_color('#dddddd')
    ax.spines['left'].set_color('#dddddd')
    ax.tick_params(axis='x', color='#dddddd')
    ax.tick_params(axis='y', color='#dddddd')

def total_states(root, state_re = "states: (\d+)"):
    with open(f"{root}/log") as f:
        for line in f:
            match = re.search(state_re, line)
            if match:
                return int(match.group(1))
    raise Exception(f"No states for {root}")


def total_transitions(root, transition_re = "transitions: (\d+)"):
    with open(f"{root}/log") as f:
        for line in f:
            match = re.search(transition_re, line)
            if match:
                return int(match.group(1))
    raise Exception(f"No transitions for {root}")


def total_runtime(root):
    with open(f"{root}/log") as f:
        for line in f:
            match = runtime_re.search(line)
            if match:
                return ((int(match.group(1)) * 60) +
                        (int(match.group(2))) +
                        int(match.group(3))/60.0)
    raise Exception(f"No runtime for {root}")


def match_prefix(expected, actual):
    prefix = []
    for e1, e2 in zip(expected, actual):
        if e1 != e2:
            return (prefix, expected)
        else:
            prefix.append(e1)
    return (prefix, expected)


def levenshtein_distance(s1, s2):
    if len(s1) > len(s2):
        s1, s2 = s2, s1
    distances = range(len(s1) + 1)
    for index2, char2 in enumerate(s2):
        newDistances = [index2+1]
        for index1, char1 in enumerate(s1):
            if char1 == char2:
                newDistances.append(distances[index1])
            else:
                newDistances.append(1 + min((distances[index1],
                                             distances[index1+1],
                                             newDistances[-1])))
        distances = newDistances
    return distances[-1]


def output_square_distance(o1, o2):
    if isinstance(o1, int) and isinstance(o2, int):
        return (o1 - o2) ** 2
    else:
        return levenshtein_distance(str(o1), str(o2)) ** 2


def outputs_distance(O1, O2):
    return sum([output_square_distance(o1, o2) for o1, o2 in zip(O1, O2)])


def to_num(o):
    if isinstance(o, int):
        return o
    else:
        return levenshtein_distance("", str(o))


def match(event):
    return event['expected'] == event['actual']


def split_trace(trace, rejected=None):
    if rejected is not None:
            return (
                    list(takewhile(match, trace)),
                    list(dropwhile(match, trace)),
                    rejected
                   )
    return (list(takewhile(match, trace)), list(dropwhile(match, trace)))


def get_info(root, fileName):
    # print(root)
    
    info = {}

    if fileName == "testLog.json":
        info['states'] = total_states(root)
        info['transitions'] = total_transitions(root)
    elif fileName == "ptaLog.json":
        # print("Doing PTA for", root)
        info['states'] = total_states(root, "PTA has (\d+) states")
        info['transitions'] = total_transitions(root, "PTA has (\d+) transitions")

    with open(f"{root}/{fileName}") as f:
        log = json.loads("".join(f.readlines()))

    info['runtime'] = total_runtime(root)

    triples = [split_trace(trace['trace'], trace['rejected']) for trace in log]
    
    # info['triples'] = [(len(x), len(y), len(z)) for x, y, z in triples]
    
    info['t1'] = [len(x)/(len(x) + len(y) + len(z)) for x, y, z in triples],
    info['t2'] = [len(y)/(len(x) + len(y) + len(z)) for x, y, z in triples],
    info['t3'] = [len(z)/(len(x) + len(y) + len(z)) for x, y, z in triples],

    # if "spaceInvaders30-gp" in root:
    #     if mean(info['t3'][0]) > 0:
    #         print("atom", root+"/testlog.json")

    # lengths = [len(t) for t, _, _ in triples]

    # Minimum number of events before we can tell the models apart - useless
    # info['min'] = min(lengths)
    # Average number of events before we can tell the models apart - useless
    # info['avg'] = mean(lengths)
    # Ultrametric from the paper - useless
    # info['ultra'] = 2**-min(lengths)
    # Mean prop. of the trace got through before we can tell the trace apart
    # info['prop'] = [len(list(filter(lambda e: e['expected'] == e['actual'], obj['trace'])))/(len(obj['trace'])+len(obj['rejected'])) for obj in log]
    info['prop'] = [(len(x) + len([e for e in y if e['expected'] == e['actual']]))/(len(x) + len(y) + len(z)) for x, y, z in triples],


    valid_traces = sum([s1 == [] and s2 == [] for _, s1, s2 in triples])
    info['sensitivity'] = valid_traces/len(log)

    rmse = sum([
                sum([
                        outputs_distance(event['expected'], event['actual'])
                        for event in obj['trace']
                    ])
                for obj in log
            ])
    rmse = math.sqrt(rmse)
    info['rmse'] = rmse

    outputs = set()
    for obj in log:
        for event in obj['trace']:
            outputs = outputs.union([to_num(o) for o in event['expected']])
            outputs = outputs.union([to_num(o) for o in event['actual']])
    info['nrmse'] = rmse/(max(outputs) - min(outputs))

    # states_covered = set()
    # for obj in log:
    #     for event in obj['trace']:
    #         states_covered.add(event['currentState'])
    #         states_covered.add(event['nextState'])
    # info['state coverage'] = len(states_covered)/info['states']
    # transitions_covered = set()
    # for obj in log:
    #     for event in obj['trace']:
    #         transitions_covered.add(tuple(event['transition']))
    # info['transition coverage'] = len(transitions_covered)/info['transitions']
    return info


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

    bp = ax1.boxplot(
            boxes,
            # medianprops={"linewidth": 0},
            # boxprops={"linewidth": 0},
            # whiskerprops={"linewidth": 0},
            # capprops={"linewidth": 0},
            widths=0.4
          )
    
    # # Shift the median lines so they look good on pdf
    # for median in bp['medians']:
    #     x, y = median.get_data()
    #     ax1.plot(x+0.003, y, color="r", linewidth=1, solid_capstyle="butt", zorder=0)
    
    # # Only draw the boxes that have a nonzero size
    # for b in bp['boxes']:
    #     x, y = b.get_data()
    #     if len(set(y)) > 1:
    #         ax1.plot(x, y, color="k", linewidth=1, zorder=4)
    
    # for whisker, cap in zip(bp['whiskers'], bp['caps']):
    #     w_x, w_y = whisker.get_data()
    #     c_x, c_y = cap.get_data()
    #     if len(set(w_y)) > 1:
    #         ax1.plot(w_x, w_y, color="k", linewidth=1)
    #         ax1.plot(c_x, c_y, color="k", linewidth=1)

    labels = [" ".join(c.replace("obfuscated", "obfuscated\n").replace("distinguish", "\nguards").replace("gp", "GP").split("-")) for c in cfgs]
    # ax1.set_xticks(range(0, len(labels)+1))
    ax1.set_xticklabels(
        labels,
        rotation=45,
        ha='right',
        va='top',
        ma='right',
        rotation_mode="anchor"
    )
    ax1.tick_params(axis='both', labelsize=10)

    axesColour(ax1)
    ax1.set_title(title)
    ax1.margins()
    
def boxPlots(column, ps, fname, systems):
    size = 0
    for p in systems:
        for c in ps[p]:
            size += 1
    
    # fig1 = plt.figure(figsize=(0.8*size, 3))
    # spec = gridspec.GridSpec(nrows=1, ncols=len(systems), width_ratios=[len(ps[p]) for p in systems])

    fig, axs = plt.subplots(nrows=1, ncols=len(systems), sharex='col', sharey='row', figsize=(0.8*size, 3))
    
    print(f"box {fname}-{column} size: {size}")
    
    title = (
        "Accepted Prefix" if column == "t1" else 
        "NRMSE" if column == "nrmse" else 
        "Runtime (Minutes)" if column == "runtime" else
        column.capitalize()
        )
    
    for i, p in enumerate(systems):
        ax = axs[i]
        ax.yaxis.set_tick_params(which='both', labelleft=True)

        cfgs = configs(p)
        if column not in ["states", "transitions", "runtime"]:
            cfgs = [c for c in cfgs if c != "MINT"]
        
        box1(column, p, cfgs, fname, r"\textsc{"+p+"} "+title, ax)


    # plt.tight_layout()
    plt.savefig(f"{homedir}/graphs/{fname}.pdf", bbox_inches='tight')
    plt.close()


def statesPlots(column, ps, fname, systems):
    size = 0
    for p in systems:
        for c in ps[p]:
            size += 1
    
    fig = plt.figure(figsize=(0.8*size, 3))
    spec = gridspec.GridSpec(nrows=1, ncols=3, width_ratios=[5, 9, 2])
    axs = [fig.add_subplot(spec[i]) for i,_ in enumerate((spec))]
    
    # fig, axs = plt.subplots(nrows=1, ncols=len(systems)+1, figsize=(0.8*size, 3))
    
    print(f"box {fname}-{column} size: {size}")
    
    title = column.capitalize()
    
    for i, p in enumerate(systems):
        ax = axs[i]
        ax.yaxis.set_tick_params(which='both', labelleft=True)

        cfgs = [c for c in configs(p) if c != "pta"]
        
        box1(column, p, cfgs, fname, r"\textsc{"+p+"} "+title, ax)
    
    ax1 = axs[len(systems)]
    ax1.yaxis.set_tick_params(which='both', labelleft=True)

    cfgs = ['pta']
    
    boxes = [data[p]['pta'][column].astype(float) for p in systems]

    ax1.boxplot(boxes, widths=0.4)
    
    labels = [r"\textsc{"+p+"}\nPTA" for p in systems]
    ax1.set_xticklabels(
        labels,
        rotation=45,
        ha='right',
        va='top',
        ma='right',
        rotation_mode="anchor"
    )
    ax1.tick_params(axis='both', labelsize=10)

    axesColour(ax1)
    ax1.set_title("PTA "+title)
    ax1.margins()
    plt.savefig(f"{homedir}/graphs/{fname}.pdf", bbox_inches='tight')
    plt.close()


def box(column, cfgs, fname, title, ps):
    if column == 't1' or column == "prop":
        boxes_aux = [data[p][c][column] for p in ps for c in cfgs if c in data[p]]
        boxes = [[item for sublist in l for item in sublist] for l in boxes_aux]
    else:
        boxes = [data[p][c][column].astype(float) for p in ps for c in cfgs if c in data[p]]
        
    fig1, ax1 = plt.subplots(figsize=(0.7*len(boxes), 3))
    ax1.set_title(title)
    
    print(f"box {fname}-{column} size: {0.7*len(boxes)}")
    
    bp = ax1.boxplot(
            boxes,
            # medianprops={"linewidth": 0},
            # boxprops={"linewidth": 0},
            # whiskerprops={"linewidth": 0},
            # capprops={"linewidth": 0}
            widths=0.4
          )
    
    # # Shift the median lines so they look good on pdf
    # for median in bp['medians']:
    #     x, y = median.get_data()
    #     ax1.plot(x+0.003, y, color="r", linewidth=1, solid_capstyle="butt", zorder=0)
    
    # # Only draw the boxes that have a nonzero size
    # for b in bp['boxes']:
    #     x, y = b.get_data()
    #     if len(set(y)) > 1:
    #         ax1.plot(x, y, color="k", linewidth=1, zorder=4)
    
    # for whisker, cap in zip(bp['whiskers'], bp['caps']):
    #     w_x, w_y = whisker.get_data()
    #     c_x, c_y = cap.get_data()
    #     if len(set(w_y)) > 1:
    #         ax1.plot(w_x, w_y, color="k", linewidth=1)
    #         ax1.plot(c_x, c_y, color="k", linewidth=1)
    
    labels = [" ".join(c.replace("obfuscated", "obfuscated\n").split("-")) for c in cfgs]
    if len(ps) > 1:
        labels = [f'{program.replace("Guards", "")}\n{c}' for program in ps for c in cfgs]
    ax1.set_xticks(range(0, len(labels)+1))
    ax1.set_xticklabels(
        [""]+labels,
        rotation=45,
        ha='right',
        va='top',
        ma='right',
        rotation_mode="anchor"
    )
    axesColour(ax1)
    ax1.tick_params(axis='both', labelsize=10)
    
    # ax1.set_ylim(ymin=0)
    ax1.margins()
    
    if column in ['sensitivity', 'prop']:
        ax1.set_ylim(ymax=1.1)

    
    plt.savefig(f"{homedir}/graphs/{fname}-{column}.pdf", bbox_inches='tight')
    plt.close()

def ts(ps, cfgs, fname, title):
    for p in ps:
        print(p, cfgs)
    
        cfgs =  [c for c in cfgs if c in data[p]]
        
        for c in cfgs:
            print(c, "t2" in data[p][c])
        
        t1Means = [mean([mean(x) for x in data[p][c]['t1']]) for c in cfgs]
        t2Means = [mean([mean(x) for x in data[p][c]['t2']]) + t1Means[i] for i, c in enumerate(cfgs)]
        t3Means = [1] * len(t2Means)
        
        if any([t > 1 for t in t2Means]):
            raise Exception("More than 1")
        
        ind = range(len(t1Means))
    
    fig1, ax1 = plt.subplots(figsize=(0.7*len(t1Means), 3))
    p3 = ax1.bar(ind, t3Means, color='red')
    p2 = ax1.bar(ind, t2Means, color='orange')
    p1 = ax1.bar(ind, t1Means, color='green')
    
    plt.title(title)
    
    ax1.set_xticks(ind)
    labels = [" ".join(c.replace("obfuscated", "obfuscated\n").split("-")) for c in cfgs]
    if len(ps) > 1:
        labels = [f"{program}\n{c}" for program in ps for c in cfgs]

    ax1.set_xticks(range(0, len(labels)+1))
    ax1.set_xticklabels(
        [""]+labels,
        rotation=45,
        ha='right',
        va='top',
        ma='right',
        rotation_mode="anchor"
    )
    axesColour(ax1)

    # plt.tight_layout()
    plt.legend((p1[0], p2[0], p3[0]),
               ('Accepted', 'Recognised', "Rejected"),
               loc='upper center',
               bbox_to_anchor=(0.5, 1.3),
               ncol=3)
    plt.savefig(f"{homedir}/graphs/{fname}-traces.pdf", bbox_inches='tight')
    plt.show()

def hist(program, config, column, xlabel=False):
    bars = data[program][config][column]
    fig1, ax1 = plt.subplots(figsize=(5, 3))

    ax1.hist(bars, bins=30)
    ttl = " ".join(config.split("-"))
    ax1.set_title(f"{program} {ttl} {column.capitalize()}")
    
    if xlabel:
        ax1.set_xlabel(xlabel)
    else:
        ax1.set_xlabel(column)

    ax1.set_ylabel("Frequency")

    if config == "t1":
        ax1.set_xticks([0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0])
    plt.show()
    # plt.savefig(f"{homedir}/graphs/{program}-{config}-{column}.pdf", bbox_inches='tight')
    # plt.close()



columns = ['states', 'transitions', 'prop', 'sensitivity', 'nrmse', 'runtime', 't1']
           # 'min', 'avg', 'ultra', 'rmse', 'state coverage', 'transition coverage', 't2', 't3']

if not os.path.exists(f"{homedir}/graphs"):
    os.mkdir(f"{homedir}/graphs")


# Load in the data from pickle if we can so we don't have to keep recalculating stuff
if os.path.exists(f"{homedir}/data.dic"):
    with open(f'{homedir}/data.dic', 'rb') as f:
        data = pickle.load(f)

# Uncomment this to append data
program = "spaceInvaders"
# Add in PTA - we don't need to loop and average as it's always the
# same for each trace set
if 'pta' not in data[program]:
    data[program]['pta'] = pd.DataFrame(columns=columns)

for i in range(1, 31):
    dd = f"{homedir}/{program}30/{i}/gp/{program}30-none-57831-60387-79031"
    if os.path.exists(dd) and "log" in os.listdir(dd):
        data[program]['pta'] = data[program]['pta'].append(pd.DataFrame(get_info(dd, "ptaLog.json"), index=[dd+"-pta"]))
    
for log in os.listdir(f"{homedir}/{program}30"):
    configurations = os.listdir(f"{homedir}/{program}30/{log}")

    for config in [c for c in configurations if c != "pta"]:
        if config not in data[program]:
            data[program][config] = pd.DataFrame(columns=columns)


        dd = f"{homedir}/{program}30/{log}/{config}"
        roots = ([f"{dd}/{d}" for d in os.listdir(dd)
                  if os.path.isdir(f"{dd}/{d}") and os.path.exists(f"{dd}/{d}/testLog.json")])

        for r in roots:
            try:
                data[program][config] = data[program][config].append(pd.DataFrame(get_info(r, "testLog.json"), index=[r]))
            except:
                print(r)

with open(f'{homedir}/data.dic', 'wb') as f:
    pickle.dump(data, f)
# End of uncomment

# if os.path.exists(f"{homedir}/mann-whitney-u.csv"):
#     os.remove(f"{homedir}/mann-whitney-u.csv")
# with open(f"{homedir}/mann-whitney-u.csv", 'w') as m:
#     print("system", "x", "y", "U", "p", "significant", file=m, sep=",")
    
# fname = "".join([p[:2] for p in systems])

# ps = {p:configs(p) for p in data}

# for column in [c for c in columns if c not in ['t2', 't3']]:
#     boxPlots(column, ps, f"{fname}-{column}-plots", systems)

# statesPlots("states", ps, f"{fname}-states-plots", systems)
# statesPlots("transitions", ps, f"{fname}-transitions-plots", systems)


# for program in data:
#     # for column in [c for c in columns if c not in ['t2', 't3']]:
#     #     box(column, [program], configs(program), program, f"{program} {column}")
#     with open(f"{homedir}/mann-whitney-u.csv", 'a') as m:
#         print(program, file=m)
#     # for x in configs(program):
#     #     for y in configs(program):
#     #         if x > y:
#     #             mwu = mannwhitneyu(data[program][x]['prop'], data[program][y]['prop'])
#     #             with open(f"{homedir}/mann-whitney-u.csv", 'a') as m:
#     #                 print("", x, y, mwu.statistic, mwu.pvalue, mwu.pvalue < 0.05, file=m, sep=",")

#     # t1 configs
#     print("\n" + program)
#     for config in configs(program):
#         # should be 30 for non-gp things and 900 otherwise
#         print("", config, len(data[program][config]['t1']))
#         # t1_bars = sorted([item for sublist in data[program][config]['t1'] for item in sublist])
#         # hist(t1_bars, program, config, 't1', "Normalised length of correct prefix")
        
#         # states_bars = sorted(data[program][config]['states'])
#         # hist(states_bars, program, config, 'states', f"Number of states for {config}")
        
#         # transitions_bars = sorted(data[program][config]['states'])
#         # hist(transitions_bars, program, config, 'transitions', f"Number of transitions for {config}")
        
#         # hist(sorted(data[program][config]['sensitivity']), program, config, 'sensitivity', f"Sensitivity for {config}")

#     # Trace correctness
#     # ts([program], configs(program), program, f"{program} Trace Parts")

#     with open(f"{homedir}/graphs/{program}-graphs.tex", 'w') as f:
#         print("\\documentclass{article}", file=f)
#         print("\\usepackage{tikz}", file=f)
#         print("\\usepackage{a4wide}", file=f)
#         print("\\begin{document}", file=f)
#         print("\\centering", file=f)
#         for column in [c for c in columns + ["traces"] if c not in ['t1', 't2', 't3']]:
#             print("\\resizebox{\\textwidth}{!}{\\input{"+program+"-"+column+".pdf}}", file=f)
#         print("\\end{document}", file=f)

# if systems == ["liftDoors", "spaceInvaders"]:
#     cfgs = ["pta", "none", "gp", "MINT"]

#     # ts(ps, cfgs, fname, "Trace Parts")
#     box("sensitivity", cfgs, fname, "Sensitivity", systems)
#     box("nrmse", cfgs, fname, "NRMSE", systems)
#     box("prop", cfgs, fname, "Proportion of Correct Events", systems)
#     box("t1", cfgs, fname, "Proportional Lengths of Accepted Prefixes", systems)
    
    
#     box("states", cfgs, fname, "States", systems)
#     box("transitions", cfgs, fname, "Transitions", systems)
    
#     box("runtime", cfgs, fname, "Runtime", systems)


# # fig, ax = plt.subplots()
# # states = list(data['drinks']['gp']['states'])
# # t1 = list([mean(y) for y in data['drinks']['gp']['sensitivity']])
# # ax.scatter(states, t1, color="b", marker='o')
# # states = list(data['drinks']['gp-distinguish']['states'])
# # t1 = list([mean(y) for y in data['drinks']['gp-distinguish']['sensitivity']])
# # ax.scatter(states, t1, color="r", marker='x')

# # ax.set_xlabel("Number of States")
# # ax.set_ylabel("Sensitivity")
# # ax.set_title("Number of States vs. Sensitivity")
# # plt.savefig(f"{homedir}/graphs/drinks-sensitivity-size.pdf", bbox_inches='tight')
# # plt.close()

# # fig, ax = plt.subplots()
# # states = list(data['spaceInvadersGuards']['gp']['states'])
# # t1 = list([mean(y) for y in data['spaceInvadersGuards']['gp']['sensitivity']])
# # ax.scatter(states, t1, color="b", marker='o')

# hist('spaceInvaders', 'MINT', 'sensitivity')
# hist('spaceInvaders', 'MINT', 'states')

# # ax.set_xlabel("Number of States")
# # ax.set_ylabel("Sensitivity")
# # ax.set_title("Number of States vs. Sensitivity")
# # plt.savefig(f"{homedir}/graphs/spaceInvaders-sensitivity-size.pdf", bbox_inches='tight')
# # plt.close()
