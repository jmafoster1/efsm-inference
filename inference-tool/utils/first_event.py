#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jun 19 09:39:25 2020

@author: michael
"""

import os
import json
from numpy import mean

root = "/home/michael/Documents/efsm-inference/inference-tool/experimental-data"
prog = "spaceInvaders30"
event = "alienHit"

occurences = []

for seed in os.listdir(f"{root}/{prog}"):
    for f in [f for f in os.listdir(f"{root}/{prog}/{seed}") if f.endswith(".json")]:
        with open(f"{root}/{prog}/{seed}/{f}") as logfile:
            log = json.loads("".join(logfile.readlines()))
        for trace in log:
            labels = list(map(lambda e: e['label'], trace))
            if event in labels:
                occurences.append(list(labels).index(event))

print(mean(occurences))
