#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Feb 13 16:34:03 2020

@author: michael
"""

import json

file = "results/liftDoors50-none-873365-958765-627334/testLog.json"

with open(file) as f:
    log = json.loads("".join(f.readlines()))

for obj in log:
    trace = obj['trace']
    states_covered = [event['state'] for event in trace]
    print(set(states_covered))
