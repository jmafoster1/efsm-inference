#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jun 14 11:30:34 2020

@author: michael
"""

import os

root = "/home/michael/Documents/efsm-inference/inference-tool/results"

for prog in [f for f in os.listdir(root) if os.path.isdir(f"{root}/{f}") and f != "graphs"]:
    for log in os.listdir(f"{root}/{prog}"):
        for config in os.listdir(f"{root}/{prog}/{log}"):
            for run in os.listdir(f"{root}/{prog}/{log}/{config}"):
                if "testLog.json" not in os.listdir(f"{root}/{prog}/{log}/{config}/{run}"):
                    with open(f"{root}/{prog}/{log}/{config}/{run}/log") as l:
                        _, s, _, p, _, g, _, o, _, u, _, _, _, df, train, test = l.readline()[26:].split()
                        base, seed = train.split("/")[2].split("-")
                        print("sbatch bessemer-run.sh", g, o, u, base, p, seed)