#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 12 10:57:50 2019

@author: michael
"""
from dateutil import parser
import matplotlib.pyplot as plt

with open('/home/michael/Desktop/log2a.log') as file:
    file.readline()
    first = file.readline().split(" ")
    epoch = parser.parse(first[0])
    print(epoch)
    x = [0]
    y = [int(first[-3])]
    for line in file:
        spl = line.split(" ")
        t = parser.parse(spl[0])
        x.append((t - epoch).seconds)
        y.append(int(spl[-3]))

print(x)

plt.scatter(x, y)
