#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jun  5 10:33:28 2020

@author: michael
"""

import glob
import sys
import re
import os

out_re = re.compile("slurm-(\d+).out")

upto = sys.argv[1]

for slurm in glob.glob("slurm-*.out"):
    if int(out_re.search(slurm).group(1)) <= int(upto):
        os.remove(slurm)
    