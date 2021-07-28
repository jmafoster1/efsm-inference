#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Mar  1 14:17:46 2021

@author: michael
"""

import pickle
import matplotlib.pyplot as plt

import random
import numpy
import pandas as pd

homedir = "/home/michael/Documents/efsm-inference/inference-tool/results"
systems = ["spaceInvaders"]
metrics = ["t1", "prop"]

with open(f'{homedir}/data.dic', 'rb') as f:
    data = pd.read_pickle(f)

# for metric in metrics:
#     for system in systems:
#         print(system, metric)
        
#         mint = ([col for col in data[system]['MINT'][metric]])
#         gp = ([col for col in data[system]['gp'][metric]])
        
#         print("ok")
        
#         mint = [item for sublist in mint for item in sublist]
#         gp = [item for sublist in gp for item in sublist]
        
#         count = {}
#         for i in mint:
#             if i not in count:
#                 count[i] = 0
#             count[i] += 1
#         print(len(count))

#         # print("gp > mint", sum([x > y for x, y in zip(gp, mint)]))
#         # print("gp >= mint", sum([x >= y for x, y in zip(gp, mint)]))
        
#         # print([x for x in data['spaceInvaders'] if x['MINT']['sensitivity'] > x['gp']['sensitivity']])
        
#         bins = numpy.linspace(0, 1, 100)
        
#         plt.hist(mint, bins, alpha=0.5, label='MINT')
#         plt.hist(gp, bins, alpha=0.5, label='GP')
        
#         plt.xlabel(metric)
#         plt.ylabel("Frequency")
#         plt.title(f"GP vs MINT {metric}")
        

        
#         plt.legend(loc='upper left')
#         plt.show()

column = "states"
instances = [(x, y, z) for x,y,z in zip(data['spaceInvaders']['MINT'][column], data['spaceInvaders']['gp'][column], data['spaceInvaders']['MINT'].index) if x > y]

# instances = [(len([((i),j) for i, j in zip(x, y) if i > j]), z) for x, y, z in instances]

ninstances = [(x, y, z) for x,y,z in zip(data['spaceInvaders']['MINT'][column], data['spaceInvaders']['gp'][column], data['spaceInvaders']['MINT'].index) if x < y]
# print("\n".join([str(x) for x in ninstances]))
print(len(ninstances))

# print("\n".join([str(x) for x in instances]))
