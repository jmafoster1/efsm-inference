#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Sep  3 11:22:31 2019

@author: michael
"""

import json

root = "/home/michael/Documents/efsm-inference/case-study/json-traces/"
fname = "mkdir"

with open(root+"/"+fname+".json") as f:
    log = json.load(f)
    for trace in log:
        for event in trace:
            event['inputs'] = [str(x) for x in event['inputs']]
            event['outputs'] = [str(x) for x in event['outputs']]

with open(root+fname+"-string.json", 'w') as f:
    print(json.dumps(log), file=f)
