#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Jun  4 16:18:32 2020

@author: michael
"""

from numpy.random import randint

with open("experimental-data/seeds", 'w') as f:
    for i in range(30):
        print(randint(10000, 99999), randint(10000, 99999), randint(10000, 99999), file=f)