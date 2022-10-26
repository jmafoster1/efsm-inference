#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Dec 28 11:06:06 2020

@author: michael
"""

import re

# import pickle

# homedir = "/home/michael/Documents/efsm-inference/inference-tool/results"

# with open(f'{homedir}/data.dic', 'rb') as f:
#     data = pickle.load(f)

# print(data['spaceInvaders']['obfuscated-x-shields-gp'].query("sensitivity > 0.04")['sensitivity'])

def clean(line):
    line = re.sub(r"</?(\w+)>", "", line)
    # line = re.sub(r"s\d+->s\d+", "", line)
    return line.replace("&#91;", "[").replace("&#93;", "]").replace("label=", "")#[2:-3]

xShieldsLines = set()
with open("results/spaceInvaders30/13/obfuscated-x-shields-gp/spaceInvaders30-obfuscated-x-shields-gp-91766-74431-95699/spaceInvaders30_obfuscated_x_shields_train_gen.dot") as f:
    for line in f:
        if "shieldHit" in line:
            xShieldsLines.add(line.strip())


xLines = set()
with open("results-orig/spaceInvaders30/13/obfuscated-x-gp/spaceInvaders30-obfuscated-x-gp-91766-74431-95699/spaceInvaders30_obfuscated_x_train_gen.dot") as f:
    for line in f:
        if "shieldHit" in line:
            xLines.add(line.strip())

for l in xShieldsLines:
    print(clean(l))

print()

for l in xLines:
    print(clean(l))
