#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Feb 11 15:05:24 2020

@author: michael
"""

import json
import numpy as np

file = "results/liftDoors50-none-873365-958765-627334/testLog.json"


def match_prefix(expected, actual):
    prefix = []
    for e1, e2 in zip(expected, actual):
        if e1 != e2:
            return prefix
        else:
            prefix.append(e1)
    return (prefix, expected)


def make_trace_pair(trace, rejected):
    expected_prefix = [(event['label'], event['inputs'], event['expected']) for event in trace]
    expected_suffix = [(event['label'], event['inputs'], event['outputs']) for event in rejected]
    actual_values = [(event['label'], event['inputs'], event['actual']) for event in trace]
    return (expected_prefix + expected_suffix, actual_values)


def make_trace_pairs(log):
    return [make_trace_pair(obj['trace'], obj['rejected']) for obj in log]


with open(file) as f:
    log = json.loads("".join(f.readlines()))
    
trace_pairs = make_trace_pairs(log)
prefixes = [match_prefix(expected, actual) for expected, actual in trace_pairs]
matching_prefixes = [x for x, y in prefixes if (len(x)/len(y)) < 1]

#for t in matching_prefixes:
#    print([f"{label}{tuple(inputs)}/{outputs}" for label, inputs, outputs in t])

lengths = [len(t) for t in matching_prefixes]
print("min:", min(lengths) if lengths != [] else None)
print("avg:", np.mean(lengths) if lengths != [] else None)
print("ultra:", 2**-min(lengths) if lengths != [] else 0)
print("mean frac got through:", np.mean([(len(x)/len(y)) for x, y in prefixes]))

correct_events = [item for sublist in [x for x, y in prefixes] for item in sublist]
total_events = [item for sublist in [y for x, y in prefixes] for item in sublist]
print("prop correct events", len(correct_events)/len(total_events))
