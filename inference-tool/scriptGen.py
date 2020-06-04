#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Jun  4 16:47:18 2020

@author: michael
"""

import os

scripts = {}

for root, dirs, files in os.walk("experimental-data/"):
    files = [os.path.join(root, file) for file in files if file.endswith(".sh")]
    for file in files:
        if os.path.basename(file) not in scripts:
            scripts[os.path.basename(file)] = ""
        scripts[os.path.basename(file)] += f"bash {file}\n"

for script in scripts:
    with open(script, 'w') as f:
        print(scripts[script], file=f)

