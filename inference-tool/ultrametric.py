#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Feb 11 15:05:24 2020

@author: michael
"""

import json
from numpy import mean
import re
import math
import os
from itertools import takewhile, dropwhile
import pandas as pd
import matplotlib.pyplot as plt
import pickle
from scipy.stats import mannwhitneyu

runtime_re = re.compile("Completed in (\d+)h (\d+)m (\d+).\d+s")


def configs(p):
    if p == "liftDoors":
        return ['pta', 'none', 'gp', 'obfuscated-time-none', 'obfuscated-time-gp']
    if p == "spaceInvaders":
        return [
            'pta', 'none', 'gp',
            'obfuscated-aliens-none', 'obfuscated-aliens-gp',
            'obfuscated-shields-none', 'obfuscated-shields-gp',
            'obfuscated-x-none', 'obfuscated-x-gp'
            ]
    return sorted(list(p.keys()))


def total_states(root, state_re = "states: (\d+)"):
    with open(f"{root}/log") as f:
        for line in f:
            match = re.search(state_re, line)
            if match:
                return int(match.group(1))


def total_transitions(root, transition_re = "transitions: (\d+)"):
    with open(f"{root}/log") as f:
        for line in f:
            match = re.search(transition_re, line)
            if match:
                return int(match.group(1))


def total_runtime(root):
    with open(f"{root}/log") as f:
        for line in f:
            match = runtime_re.search(line)
            if match:
                return ((int(match.group(1)) * 60) +
                        (int(match.group(2))) +
                        int(match.group(3))/60.0)


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
    info = {}

    if fileName == "testLog.json":
        info['states'] = total_states(root)
        info['transitions'] = total_transitions(root)
    elif fileName == "ptaLog.json":
        info['states'] = total_states(root, "PTA has (\d+) states")
        info['transitions'] = total_transitions(root, "PTA has (\d+) transitions")

    with open(f"{root}/{fileName}") as f:
        log = json.loads("".join(f.readlines()))

    info['runtime'] = total_runtime(root)

    triples = [split_trace(trace['trace'], trace['rejected']) for trace in log]
    info['t1'] = [len(x)/(len(x) + len(y) + len(z)) for x, y, z in triples],
    info['t2'] = [len(y)/(len(x) + len(y) + len(z)) for x, y, z in triples],
    info['t3'] = [len(z)/(len(x) + len(y) + len(z)) for x, y, z in triples],

    # if "spaceInvaders30-gp" in root:
    #     if mean(info['t3'][0]) > 0:
    #         print("atom", root+"/testlog.json")

    lengths = [len(t) for t, _, _ in triples]

    # Minimum number of events before we can tell the models apart - useless
    info['min'] = min(lengths)
    # Average number of events before we can tell the models apart - useless
    info['avg'] = mean(lengths)
    # Ultrametric from the paper - useless
    info['ultra'] = 2**-min(lengths)
    # Mean prop. of the trace got through before we can tell the trace apart
    info['prop'] = mean(
            [len(list(filter(lambda e: e['expected'] == e['actual'], obj['trace'])))/(len(obj['trace'])+len(obj['rejected'])) for obj in log])

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

    states_covered = set()
    for obj in log:
        for event in obj['trace']:
            states_covered.add(event['currentState'])
            states_covered.add(event['nextState'])
    info['state coverage'] = len(states_covered)/info['states']
    transitions_covered = set()
    for obj in log:
        for event in obj['trace']:
            transitions_covered.add(tuple(event['transition']))
    info['transition coverage'] = len(transitions_covered)/info['transitions']
    return info

def box(column, ps, cfgs, fname, title):
    if column == 'runtime':
        cfgs = [c for c in cfgs if c != 'pta']
    
    fig1, ax1 = plt.subplots(figsize=(0.7*len(configs(program)), 3))
    ax1.set_title(title)
    

    if column == 't1':
        boxes_aux = [programs[program][config][column] for program in ps for config in cfgs]
        boxes = []
        for l in boxes_aux:
            boxes.append([item for sublist in l for item in sublist])
    else:
        boxes = [programs[program][config][column].astype(float) for program in ps for config in cfgs]

    bp = ax1.boxplot(
            boxes,
            medianprops={"linewidth": 0},
            boxprops={"linewidth": 0},
            whiskerprops={"linewidth": 0},
            capprops={"linewidth": 0}
         )
    
    # Shift the median lines so they look good on pdf
    for median in bp['medians']:
        x, y = median.get_data()
        ax1.plot(x+0.003, y, color="k", linewidth=1, solid_capstyle="butt", zorder=0)
    
    # Only draw the boxes that have a nonzero size
    for b in bp['boxes']:
        x, y = b.get_data()
        if len(set(y)) > 1:
            ax1.plot(x, y, color="k", linewidth=1, zorder=4)
    
    for whisker, cap in zip(bp['whiskers'], bp['caps']):
        w_x, w_y = whisker.get_data()
        c_x, c_y = cap.get_data()
        if len(set(w_y)) > 1:
            ax1.plot(w_x, w_y, color="k", linewidth=1)
            ax1.plot(c_x, c_y, color="k", linewidth=1)
    
    labels = [" ".join(c.replace("obfuscated", "obfuscated\n").split("-")) for c in cfgs]
    if len(ps) > 1:
        labels = [f"{program}\n{c}" for program in ps for c in cfgs]
    ax1.set_xticklabels(
        labels,
        rotation=45,
        ha='right',
        va='top',
        ma='right',
        rotation_mode="anchor"
    )
    
    ax1.set_ylim(ymin=0)
    
    plt.savefig(f"{homedir}/graphs/{fname}-{column}.pdf", bbox_inches='tight')
    plt.close()

def ts(ps, cfgs, fname, title):
    t1Means = [mean([mean(x) for x in programs[ps[0]][c]['t1']]) for c in cfgs]
    t2Means = [mean([mean(x) for x in programs[ps[0]][c]['t2']]) + t1Means[i] for i, c in enumerate(cfgs)]
    
    for p in ps[1:]:
        t1Means += [mean([mean(x) for x in programs[p][c]['t1']]) for i, c in enumerate(cfgs, start=len(cfgs))]
        t2Means += [mean([mean(x) for x in programs[p][c]['t2']]) + t1Means[i] for i, c in enumerate(cfgs, start=len(cfgs))]
    
    t3Means = [1] * len(t2Means)
    
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
    ax1.set_xticklabels(
        labels,
        rotation=45,
        ha='right',
        va='top',
        ma='right',
        rotation_mode="anchor"
    )

    # plt.tight_layout()
    plt.legend((p1[0], p2[0], p3[0]),
               ('Accepted', 'Recognised', "Rejected"),
               loc='upper center',
               bbox_to_anchor=(0.5, 1.3),
               ncol=3)
    plt.savefig(f"{homedir}/graphs/{fname}-traces.pdf", bbox_inches='tight')
    plt.show()

def hist(bars, program, config, column, xlabel=False):

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
    plt.tight_layout()
    plt.savefig(f"{homedir}/graphs/{program}-{config}-{column}.pdf", bbox_inches='tight')
    plt.close()



columns = ['states', 'transitions', 'min', 'avg', 'ultra', 'prop',
           'sensitivity', 'rmse', 'nrmse', 'state coverage', 'runtime',
           'transition coverage', 't1', 't2', 't3']

programs = {"liftDoors":{}, "spaceInvaders":{}}

homedir = "/home/michael/Documents/efsm-inference/inference-tool/results"

if not os.path.exists(f"{homedir}/graphs"):
    os.mkdir(f"{homedir}/graphs")


# Load in the data from pickle if we can so we don't have to keep recalculating stuff
if os.path.exists(f"{homedir}/programs.dic"):
    with open(f'{homedir}/programs.dic', 'rb') as f:
        programs = pickle.load(f)
else:
    for program in programs:
        # Add in PTA - we don't need to loop and average as it's always the
        # same for each trace set
        if 'pta' not in programs[program]:
            programs[program]['pta'] = pd.DataFrame(columns=columns)
            
        for log in os.listdir(f"{homedir}/{program}30"):
            configurations = os.listdir(f"{homedir}/{program}30/{log}")

            for config in configurations:
                if config not in programs[program]:
                    programs[program][config] = pd.DataFrame(columns=columns)


                dd = f"{homedir}/{program}30/{log}/{config}"
                roots = ([f"{dd}/{d}" for d in os.listdir(dd)
                          if os.path.isdir(f"{dd}/{d}") and os.path.exists(f"{dd}/{d}/testLog.json")])

                # TODO: DELETE THIS WHEN DRAWING ACTUAL RESULTS
                # It just stops it erroring for stuff which timed out
                if roots == []:
                    continue

                for r in roots:
                    programs[program][config] = programs[program][config].append(pd.DataFrame(get_info(r, "testLog.json"), index=[r]))

            # TODO: DELETE THIS WHEN DRAWING ACTUAL RESULTS
            # It just stops it erroring for stuff which timed out
            if roots == []:
                print(dd)
                continue
            programs[program]['pta'] = programs[program]['pta'].append(pd.DataFrame(get_info(roots[0], "ptaLog.json"), index=[roots[0]+"-pta"]))

    with open(f'{homedir}/programs.dic', 'wb') as f:
        pickle.dump(programs, f)

if os.path.exists(f"{homedir}/mann-whitney-u.csv"):
    os.remove(f"{homedir}/mann-whitney-u.csv")
with open(f"{homedir}/mann-whitney-u.csv", 'w') as m:
    print("system", "x", "y", "U", "p", "significant", file=m, sep=",")

for program in programs:
    for column in [c for c in columns if c not in ['t2', 't3']]:
        box(column, [program], configs(program), program, f"{program} {column}")
    with open(f"{homedir}/mann-whitney-u.csv", 'a') as m:
        print(program, file=m)
    for x in configs(program):
        for y in configs(program):
            if x > y:
                mwu = mannwhitneyu(programs[program][x]['prop'], programs[program][y]['prop'])
                with open(f"{homedir}/mann-whitney-u.csv", 'a') as m:
                    print("", x, y, mwu.statistic, mwu.pvalue, mwu.pvalue < 0.05, file=m, sep=",")

    # t1 configs
    print("\n" + program)
    for config in configs(program):
        # should be 30 for non-gp things and 900 otherwise
        print("", config, len(programs[program][config]['t1']))
        t1_bars = sorted([item for sublist in programs[program][config]['t1'] for item in sublist])
        hist(t1_bars, program, config, 't1', "Normalised length of correct prefix")
        
        states_bars = sorted(programs[program][config]['states'])
        hist(states_bars, program, config, 'states', f"Number of states for {config}")
        
        transitions_bars = sorted(programs[program][config]['states'])
        hist(transitions_bars, program, config, 'transitions', f"Number of transitions for {config}")

    # Trace correctness
    ts([program], configs(program), program, f"{program} Trace Parts")

    with open(f"{homedir}/graphs/{program}-graphs.tex", 'w') as f:
        print("\\documentclass{article}", file=f)
        print("\\usepackage{tikz}", file=f)
        print("\\usepackage{a4wide}", file=f)
        print("\\begin{document}", file=f)
        print("\\centering", file=f)
        for column in [c for c in columns + ["traces"] if c not in ['t1', 't2', 't3']]:
            print("\\resizebox{\\textwidth}{!}{\\input{"+program+"-"+column+".pdf}}", file=f)
        print("\\end{document}", file=f)

cfgs = ["pta", "none", "gp"]
ps = list(programs.keys())

ts(ps, cfgs, "ldsi", "Trace Parts")
box("sensitivity", programs, cfgs, "ldsi", "Sensitivity")
box("nrmse", programs, cfgs, "ldsi", "NRMSE")
box("states", programs, cfgs, "ldsi", "States")
box("transitions", programs, cfgs[1:], "ldsi-no-pta", "Transitions")
box("runtime", programs, cfgs, "ldsi", "Runtime")
box("prop", programs, cfgs, "ldsi", "Proportion of Correct events")

box("t1", programs, cfgs, "ldsi", "Proportional Lengths of Accepted Prefixes")

