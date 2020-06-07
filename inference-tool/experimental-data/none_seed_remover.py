#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Jun  6 11:14:15 2020

@author: michael
"""

import os

for root, dirs, files in os.walk("."):
    files = [f for f in files if "none-submissions.sh" in f]
    for name in files:
        path = os.path.join(root, name)
        with open(path) as f:
            lines = [l.strip() for l in f.readlines()]
        with open(path, 'w') as f:
            print(lines[0], file=f)
            for line in lines[1:]:
                print("#"+line, file=f)
            
        
