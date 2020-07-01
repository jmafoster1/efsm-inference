#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jun  5 10:18:43 2020

Checks all of the slurm outfiles for any jobs that timed out

@author: michael
"""

import os

for slurm in os.listdir("/tmp/slurm/"):
    with open(f"/tmp/slurm/{slurm}") as f:
        command = f.readline().strip()
        for line in f:
            if "TIME LIMIT" in line:
                print(f"# {slurm}")
                args = command.split(" ")[1:]
                print(f"rm -r results/{args[4]}/{args[6]}/{args[5]}/{args[4]}-{args[5]}-{args[1]}-{args[2]}-{args[3]}; {command}")
                break
