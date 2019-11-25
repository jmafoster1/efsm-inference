#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Nov 19 09:50:36 2019

@author: michael
"""
import re
import os

root = "."


def count_values(xs):
    counts = {}
    for x in xs:
        if x in counts:
            counts[x] += 1
        else:
            counts[x] = 1
    return counts


def get_best_experiments(xs):
    best = min(xs)
    best_indices = []
    for i, v in enumerate(xs):
        if v == best:
            best_indices.append(i+1)
    return best_indices


def get_num_states(d):
    with open(f"{root}/{d}/log") as f:
        num_states_line = f.readlines()[-2]
        return int(re.search("Nata\((\d+)\)", num_states_line)[1])


states_record = [get_num_states(i) for i in os.listdir() if i.startswith("dotfiles")]

print(count_values(states_record))
print(get_best_experiments(states_record))
