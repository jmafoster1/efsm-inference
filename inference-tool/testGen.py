#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 17 09:17:15 2020

@author: michael
"""

import random

testfile = "liftDoors2"

randoms = set()

for i in range(30):
    s = (random.randint(0, 1000000), random.randint(0, 1000000), random.randint(0, 1000000))
    while s in randoms:
        s = (random.randint(0, 1000000), random.randint(0, 1000000), random.randint(0, 1000000))
    randoms.add(s)

with open(f"{testfile}-submissions.sh", 'w') as f:
    for g, p, u in randoms:
        print(f"sbatch bessemer-run.sh {g} {p} {u} {testfile}", file=f)