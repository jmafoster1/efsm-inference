#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Feb 11 15:05:24 2020

@author: michael
"""

import json
import numpy as np

file = "results/liftDoors2-0-0-0/testLog.json"


def match_prefix(expected, actual):
    prefix = []
    for e1, e2 in zip(expected, actual):
        if e1 != e2:
            return prefix
        else:
            prefix.append(e1)
    if len(prefix) < len(expected):
        return prefix


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

matching_prefixes = [x for x in [match_prefix(expected, actual) for expected, actual in trace_pairs] if x is not None]

for t in matching_prefixes:
    print([f"{label}{tuple(inputs)}/{outputs}" for label, inputs, outputs in t])

lengths = [len(t) for t in matching_prefixes]
print("min:", min(lengths) if lengths != [] else None)
print("avg:", np.mean(lengths) if lengths != [] else None)
print("ultra:", 2**-min(lengths) if lengths != [] else 0)

zipped = zip(lengths, trace_pairs)
