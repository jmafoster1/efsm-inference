#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Feb 11 15:05:24 2020

@author: michael
"""

import json
import numpy as np
import re
import math
import glob
import os

state_re = re.compile("\d*:\d*:\d*.\d* \[main\] INFO  ROOT - states: (\d+)")
transition_re = re.compile("\d*:\d*:\d*.\d* \[main\] INFO  ROOT - transitions: (\d+)")

root = "results/liftDoors30-obfuscated-time-gp-*/"


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


def make_trace_pair(trace, rejected):
    expected_prefix = [(event['label'], event['inputs'], event['expected']) for event in trace]
    expected_suffix = [(event['label'], event['inputs'], event['outputs']) for event in rejected]
    actual_values = [(event['label'], event['inputs'], event['actual']) for event in trace]
    return (expected_prefix + expected_suffix, actual_values)


def make_trace_pairs(log):
    return [make_trace_pair(obj['trace'], obj['rejected']) for obj in log]


roots = ([d for d in glob.glob(root) if os.path.isdir(d) and os.path.exists(root + "testLog.json")])

for root in roots:
    print("==================================================================")
    print(root)
    with open(root + "testLog.json") as f:
        log = json.loads("".join(f.readlines()))
    
    trace_pairs = make_trace_pairs(log)
    prefixes = [match_prefix(expected, actual) for expected, actual in trace_pairs]
    matching_prefixes = [x for x, y in prefixes if (len(x)/len(y)) < 1]
    
    #for t in matching_prefixes:
    #    print([f"{label}{tuple(inputs)}/{outputs}" for label, inputs, outputs in t])
    
    print("states:", total_states())
    print("transitions:", total_transitions())
    print()
    
    lengths = [len(t) for t in matching_prefixes]
    # Minimum number of events before we can tell the models apart - useless
    print("min:", min(lengths) if lengths != [] else None)
    # Average number of events before we can tell the models apart - useless
    print("avg:", np.mean(lengths) if lengths != [] else None)
    # Ultrametric from the paper - useless
    print("ultra:", 2**-min(lengths) if lengths != [] else 0)
    # Mean proportion of the trace got through before we can tell the trace apart
    print("mean frac got through:", np.mean([(len(x)/len(y)) for x, y in prefixes]))
    
    correct_events = [item for sublist in [x for x, y in prefixes] for item in sublist]
    total_events = [item for sublist in [y for x, y in prefixes] for item in sublist]
    print("prop correct events", len(correct_events)/len(total_events))
    
    valid_traces = sum([len(x)/len(y) == 1 for x, y in prefixes])
    print("precision:", valid_traces/len(prefixes))
    
    rmse = 0
    for obj in log:
        rmse += sum([outputs_distance(event['expected'], event['actual']) for event in obj['trace']])
    rmse = math.sqrt(rmse)
    print("rmse:", rmse)
    
    outputs = set()
    for obj in log:
        for event in obj['trace']:
            outputs = outputs.union(set([to_num(o) for o in event['expected']]))
            outputs = outputs.union(set([to_num(o) for o in event['actual']]))
    print("nrmse:", rmse/(max(outputs) - min(outputs)))
    
    print()
    states_covered = set()
    for obj in log:
        for event in obj['trace']:
            states_covered.add(event['currentState'])
            states_covered.add(event['nextState'])
    print("state coverage:", len(states_covered)/total_states())
    #print("states covered:", states_covered)
    
    transitions_covered = set()
    for obj in log:
        for event in obj['trace']:
            transitions_covered.add(tuple(event['transition']))
    print("transition coverage:", len(transitions_covered)/total_transitions())
    print()
