#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 17 09:17:15 2020

@author: michael
"""

import random
import os
import glob

root = "experimental-data"
testfile = "liftDoors30"
numRepeats = 30
preprocessors = ["gp", "none"]

randoms = set()

for i in range(numRepeats):
    s = (random.randint(0, 1000000), random.randint(0, 1000000), random.randint(0, 1000000))
    while s in randoms:
        s = (random.randint(0, 1000000), random.randint(0, 1000000), random.randint(0, 1000000))
    randoms.add(s)

datafiles = [os.path.splitext(os.path.basename(n))[0] for n in glob.glob(f"{root}/{testfile}*train.json")]

for d in datafiles:
    for pp in preprocessors:
        with open(f"{d.replace('-train', '')}-{pp}-submissions.sh", 'w') as f:
            for g, p, u in randoms:
                print(f"sbatch bessemer-run.sh {g} {p} {u} {d.replace('-train', '')} {pp}", file=f)
