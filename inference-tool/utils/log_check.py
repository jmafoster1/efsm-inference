#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jun 14 11:30:34 2020

@author: michael
"""

import os

root = "/home/michael/Documents/efsm-inference/inference-tool/results"
# root = "/home/michael/Downloads/fuzz_results/results"

programs = [
    "spaceInvaders30",
    # "drinks30",
    # "liftDoors30",
    # "spaceInvadersGuards30"
    ]

with open("/home/michael/Desktop/runagain.sh", 'w') as f:
    for prog in programs:
        for log in os.listdir(f"{root}/{prog}"):
            for config in os.listdir(f"{root}/{prog}/{log}"):
                for run in os.listdir(f"{root}/{prog}/{log}/{config}"):
                    with open(f"{root}/{prog}/{log}/{config}/{run}/log") as f:
                        if "Completed" not in "".join(f.readlines()):
                            p, g, o, u = run.split("-")[-4:]
                            cfg = "-".join(run.split("-")[:-4])
                            # print(f"sbatch bessemer-run.sh {g} {o} {u} {cfg} {p} {log}")
                            print(f"rm -r {root}/{prog}/{log}/{config}/{run}")

                    # if "testLog.json" not in os.listdir(f"{root}/{prog}/{log}/{config}/{run}"):
                        p, g, o, u = run.split("-")[-4:]
                        cfg = "-".join(run.split("-")[:-4])
    
                        # print(p, g, o, u)
                        # print(f"{prog} {log} {config} {run}")
                        # print(f"sbatch bessemer-run.sh {g} {o} {u} {cfg} {p} {log}", file=f)
                        # with open(f"{root}/{prog}/{log}/{config}/{run}/log") as l:
                        #     print(l.readline()[26:])