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
import glob
import os
from itertools import takewhile, dropwhile
import pandas as pd
import matplotlib.pyplot as plt

state_re = re.compile("INFO  ROOT - states: (\d+)")
transition_re = re.compile("INFO  ROOT - transitions: (\d+)")

root = "results/spaceInvaders30-obfuscated-x-gp-*/"


def total_states():
    with open(root + "log") as f:
        for line in f:
            match = state_re.search(line)
            if match:
                return int(match.group(1))


def total_transitions():
    with open(root + "log") as f:
        for line in f:
            match = transition_re.search(line)
            if match:
                return int(match.group(1))


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
    return (
            list(takewhile(match, trace)),
            list(dropwhile(match, trace))
           )


roots = ([d for d in glob.glob(root)
          if os.path.isdir(d) and os.path.exists(d + "testLog.json")])

data = pd.DataFrame(
        columns=['states', 'transitions', 'min', 'avg', 'ultra', 'prop',
                 'precision', 'rmse', 'nrmse', 'state coverage',
                 'transition coverage'])

for root in roots:
    info = {}
    with open(root + "testLog.json") as f:
        log = json.loads("".join(f.readlines()))

    info['states'] = total_states()
    info['transitions'] = total_transitions()

    triples = [split_trace(trace['trace'], trace['rejected']) for trace in log]
    lengths = [len(t) for t, _, _ in triples]

    # Minimum number of events before we can tell the models apart - useless
    info['min'] = min(lengths) if lengths != [] else None
    # Average number of events before we can tell the models apart - useless
    info['avg'] = mean(lengths) if lengths != [] else None
    # Ultrametric from the paper - useless
    info['ultra'] = 2**-min(lengths) if lengths != [] else 0
    # Mean prop. of the trace got through before we can tell the trace apart
    info['prop'] = mean(
            [len(p)/(len(p) + len(s1) + len(s2)) for p, s1, s2 in triples])

    valid_traces = sum([s1 == [] and s2 == [] for _, s1, s2 in triples])
    info['precision'] = valid_traces/len(log)

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
    info['state coverage'] = len(states_covered)/total_states()

    transitions_covered = set()
    for obj in log:
        for event in obj['trace']:
            transitions_covered.add(tuple(event['transition']))
    info['transition coverage'] = len(transitions_covered)/total_transitions()
    data = data.append(pd.DataFrame(info, index=[root]))

fig1, ax1 = plt.subplots()
ax1.set_title('Basic Plot')
ax1.boxplot(data.states.astype(int))
ax1.boxplot(data.transitions.astype(int))
