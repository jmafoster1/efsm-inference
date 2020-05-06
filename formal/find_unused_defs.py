#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Apr 29 13:27:39 2020

@author: michael
"""

import os
import re

def_re = re.compile("(definition|fun|function|abbreviation) ?(\w+) (::)")

dec_re = re.compile("(definition|fun|function|abbreviation) \"?(\w+) (\w|=)")


def find_unused_defs(path):
    defs = []
    with open(path) as f:
        content = f.readlines()
        joined = "\n".join(content)
        for line in content:
            match = def_re.search(line)
            if match is not None:
                if joined.count(match.group(2)) < 3:
                    defs.append(match.group(2))
    return defs
                    

for root, dirs, files in os.walk(".", topdown=False):
    files = [f for f in files if f.endswith(".thy")]
    for name in files:
        path = os.path.join(root, name)
        defs = find_unused_defs(path)
        if defs:
            print(path)
            for d in defs:
                print("  ", d)
        
