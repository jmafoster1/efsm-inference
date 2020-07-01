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
                        print(l.readline()[26:])