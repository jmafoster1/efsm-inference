#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Mar  1 10:30:27 2020

@author: michael
"""

import json

root = "/home/michael/Documents/efsm-inference/inference-tool/experimental-data/"
file = "spaceInvaders5-test.json"

with open(root+file) as f:
    parsed = json.loads("".join(f.readlines()))

newLog = []
for trace in parsed:
    lastLabel = ""
    moves = 1
    i = 0
    newTrace = []
    while i < len(trace):
        event = trace[i]
        label = event['label']
        inputs = event['inputs']
        outputs = event['outputs']

        if label in ["moveEast", "moveWest"]:
            while i+1 < len(trace) and trace[i+1]['label'] == label:
                outputs = trace[i+1]['outputs']
                i += 1
                moves += 1
            event['inputs'].append(moves)
        
        event['outputs'] = outputs
        
        moves = 1
        lastLabel = event['label']
        i += 1
        newTrace.append(event)
    newLog.append(newTrace)

with open(root+"spaceInvaders5-new-test.json", 'w') as f:
    print(json.dumps(newLog, indent=2), file=f)
