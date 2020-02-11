#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Feb 11 12:58:30 2020

@author: michael
"""

import json

inputFile = "dotfiles/testLog-soft.json"

def get_metric(trace, rejected):
    i = 0
    for event in trace:
        if event['expected'] != event['actual']:
            return 2**-i
        else:
            i += 1
    if i == len(trace) + len(rejected):
        return 0
    else:
        return 2**-i

with open(inputFile) as f:
    parsed = json.loads("".join(f.readlines()))

metrics = [get_metric(trace, rejected) for trace, rejected in [(obj['trace'], obj['rejected']) for obj in parsed]]

print(metrics)
