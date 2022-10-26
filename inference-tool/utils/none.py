#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Sep  6 08:47:38 2020

@author: michael
"""

from os import listdir as ls

root = "/home/michael/Documents/efsm-inference/inference-tool/results"

programs = [
    "spaceInvaders30",
    "drinks30",
    "liftDoors30",
    "spaceInvadersGuards30",
    ]

with open("/tmp/del.sh", 'w') as f:
    for p in programs:
        print(p)
        for l in range(1, 31):
            print(" ", l)
            nones = [d for d in ls(f"{root}/{p}/{l}") if "none" in d]
            for n in nones:
                if n in ls(f"{root}/{p}/{l}"):
                    for s in ls(f"{root}/{p}/{l}/{n}"):
                        if "57831-60387-79031" not in s:
                            print(f"rm -r {root}/{p}/{l}/{n}/{s}", file=f)