#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jun 21 10:45:14 2020

@author: michael
"""

import os
import json
import shutil

root = "/home/michael/Documents/efsm-inference/inference-tool/experimental-data"
prog = "spaceInvaders30"

occurences = []

for seed in os.listdir(f"{root}/{prog}"):
    for f in [f for f in os.listdir(f"{root}/{prog}/{seed}") if f.endswith(".json")]:
        with open(f"{root}/{prog}/{seed}/{f}") as logfile:
            log = json.loads("".join(logfile.readlines()))
        newlog = []
        for trace in log:
            last = trace[-1]
            trace[-2]['outputs'] = [last['label']]
        if not os.path.exists(f"{root}/{prog}-guards/{seed}"):
            os.mkdir(f"{root}/{prog}-guards/{seed}")
        with open(f"{root}/{prog}-guards/{seed}/{f}", 'w') as logfile:
            print(json.dumps([t[:-1] for t in log], indent=2), file=logfile)
    for f in [f for f in os.listdir(f"{root}/{prog}/{seed}") if f.endswith(".sh")]:
        shutil.copy(f"{root}/{prog}/{seed}/{f}", f"{root}/{prog}-guards/{seed}/{f}")
