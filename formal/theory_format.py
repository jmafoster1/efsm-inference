#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Apr 26 10:21:09 2020

@author: michael
"""

import re
import os

lemma_re = re.compile("lemma (\w+)(( ?\[simp\])?):\n")

def format(file):
    with open(file) as f:
        content = "".join(f.readlines())
    replaced = lemma_re.sub(r'lemma \1\2: ', content)
    with open(file, 'w') as f:
        print(replaced, file=f)



for root, dirs, files in os.walk(".", topdown=False):
    files = [f for f in files if f.endswith(".thy")]
    for name in files:
        path = os.path.join(root, name)
        print(path)
        format(path)
        
