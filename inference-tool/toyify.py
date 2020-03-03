#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Mar  2 11:37:44 2020

@author: michael
"""

import json

files_to_do = ["train", "test"]
num = 5

for file in files_to_do:

    with open("/home/michael/Documents/efsm-inference/inference-tool/experimental-data/spaceInvaders"+str(num)+"-"+file+".json") as f:
        parsed = json.loads("".join(f.readlines()))
    
    newLog = []
    for trace in parsed:
        newTrace = []
        for event in trace:
            if "move" in event['label'] and event['inputs'] == event['outputs']:
                continue
            elif event['label'] in ["addAlien", "launchMissile"]:
                continue
            else:
                newTrace.append(event)
        print(len(trace), len(newTrace))
        newLog.append(newTrace)
    
    with open("/home/michael/Documents/efsm-inference/inference-tool/experimental-data/spaceInvaders"+str(num)+"-toy-"+file+".json", 'w') as f:
        print(json.dumps(newLog), file=f)