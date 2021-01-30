#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Dec 11 10:37:30 2020

@author: michael
"""

import os
import json


def obfuscate(source, obfuscations, output):
    with open(source) as f:
        log = json.loads("".join(f.readlines()))
    for trace in log:
        for event in trace:
            for label in obfuscations:
                if label in event['label']:
                    event['inputs'] = obfuscations[label](event['inputs'])
    with open(output, 'w') as f:
        print(json.dumps(log, indent=2), file=f)

aliensShields = {"start": lambda i: [i[0]], "alienHit": lambda i: [], "shieldHit": lambda i: []}
aliensX = {"start": lambda i: [i[1]], "alienHit": lambda i: [], "move": lambda i: []}
xShields = {"start": lambda i: [i[2]], "move": lambda i: [], "shieldHit": lambda i: []}

for d in os.listdir("."):
    obfuscated = "aliens-x"
    if os.path.isdir(d):
        num = d.split("-")[-1]
        print(num)
        with open("../seeds") as s:
            seeds = [x.strip() for x in s.readlines()]
        with open(f"{d}/spaceInvaders30-obfuscated-{obfuscated}-submissions-gp.sh", 'w') as f:
            for seed in seeds:
                print(f"sbatch bessemer-run.sh {seed} spaceInvaders30-obfuscated-{obfuscated} gp {num}", file=f)
        # obfuscate(d+"/spaceInvaders30-train.json", xShields, d+"/spaceInvaders30-obfuscated-x-shields-train.json")
        # obfuscate(d+"/spaceInvaders30-test.json", xShields, d+"/spaceInvaders30-obfuscated-x-shields-test.json")
