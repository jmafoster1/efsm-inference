#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Oct  2 09:38:54 2022

@author: michael
"""
import re
import pydot

logfile = "dotfiles/log"

output_re = re.compile(r"output_and_update for (\d+) \[(\d+)\](.+)")

matches = []
with open(logfile) as f:
    for line in f:
        match = output_re.search(line)
        if match:
            matches.append((match.group(2), match.group(1), match.group(3)))

graph = pydot.Dot('log', graph_type='digraph')

for inx in range(len(matches)-1):
    i1, o1, t1 = matches[inx]
    i2, o2, t2 = matches[inx+1]
    if (i1, o1) != (i2, o2):
        graph.add_edge(pydot.Edge(f'{i1}[{o1}]', f'{i2}[{o2}]'))

with open(logfile+".dot", 'w') as f:
    print(graph, file=f)
