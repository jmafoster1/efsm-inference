#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Feb 11 15:05:24 2020

@author: michael
"""

import json
import numpy as np

file = "results/liftDoors2-0-0-0/testLog.json"

def match_prefix(T):
    t1, t2 = T
    prefix = []
    for e1, e2 in zip(t1, t2):
        if e1 == e2:
            prefix.append(e1)
        else:
            break
    return prefix


def make_trace_pair(trace):
    return ([(event['label'], event['inputs'], event['expected']) for event in trace],
            [(event['label'], event['inputs'], event['actual']) for event in trace])


def make_trace_pairs(log):
    return [match_prefix(make_trace_pair(obj['trace'])) for obj in log]


with open(file) as f:
    log = json.loads("".join(f.readlines()))
    
trace_pairs = make_trace_pairs(log)

for t in trace_pairs:
    print([f"{label}{tuple(inputs)}/{outputs}" for label, inputs, outputs in t])

lengths = [len(t) for t in trace_pairs]
print("min:", min(lengths))
print("avg:", np.mean(lengths))
print("ultra:", 2**-min(lengths))
