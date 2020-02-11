#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Feb  7 10:48:08 2020

@author: michael
"""

import json
import math

testLog = "dotfiles/testLog.json"


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


def minus(v1, v2):
    if isinstance(v1, int) and isinstance(v2, int):
        return v1 - v2
    return levenshtein_distance(str(v1), str(v2))


def error(v1):
    if isinstance(v1, int):
        return v1
    return levenshtein_distance(str(v1), "")


# This assumes the two lists are the same length
def square_error(l1, l2):
    if len(l1) != len(l2):
        raise Exception('Cannot calculate the error for lists of nonequal length')
    return sum([minus(x1, x2) ** 2 for x1, x2 in zip(l1, l2)])


def flattenTraceOuts(trace, rejected):
    return [error(item) for event in trace for item in event['expected'] + event['actual']] + [error(item) for event in rejected for item in event['outputs']]


with open(testLog) as f:
    content = "".join(f.readlines())
    parsed = json.loads(content)

total = 0
numEvents = 0
outputs = []

for run in parsed:
    trace = run['trace']
    rejected = run['rejected']

    outputs += flattenTraceOuts(trace, rejected)

    numEvents += len(trace) + len(rejected)
    total += sum([square_error(event['expected'], event['actual']) for event in trace])
    total += sum([sum([error(p) ** 2 for p in event['outputs']]) for event in rejected])

rmse = math.sqrt(total/numEvents)
nrmse = rmse/(max(outputs) - min(outputs))
print("RMSE =", rmse)
print("NRMSE =", nrmse)
