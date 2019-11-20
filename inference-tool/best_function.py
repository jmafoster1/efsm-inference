#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Nov 20 11:09:35 2019

@author: michael
"""
import re

num_repeats = 100
root = "."

ts = re.compile("training set: {((\[(\w+=[\w-]+(, )?)*\]=\[(\w+=\w+(, )?)*\](, )?)*)}")
target = re.compile("(\[((\w+=\w+(, )?)*)\])=(\[((\w+=\w+(, )?)*)\])")
best = re.compile("Best function is: (.+)")

def assign(xs):
    return (xs[0], xs[1])


def addTo(funs, train, fun):
    if train in funs and fun:
        if fun in funs[train]:
            funs[train][fun] += 1
        else:
            funs[train][fun] = 1
    elif fun:
        funs[train] = {fun: 1}


outputs = {}
updates = {}
guards = {}

for i in range(num_repeats):
    print(f"dotfiles-{i+1}")
    with open(f"{root}/dotfiles-{i+1}/log") as f:
        train = None
        fun = None
        current = None
        for line in f:
            if "training" in line:
#                print(line.strip())
                match = ts.search(line)
                train = match.group(1)
                if "Output" in line:
                    current = outputs
                if "Update" in line:
                    current = updates
                if "Guard" in line:
                    current = guards
#                print(line.strip())
#                for x in target.finditer(train):
#                    print([assign(asg.split("=")) for asg in x.group(2).split(", ") if "=" in x.group(2)], "=", [assign(asg.split("=")) for asg in x.group(6).split(", ")])
            if "function" in line:
                fun = best.search(line).group(1)
                addTo(current, train, fun)
#                print(best.search(line).group(1))
#                print(train, ":", fun)
#                print()

#            if train in funs and fun:
#                if fun in funs[train]:
#                    funs[train][fun] += 1
#                else:
#                    funs[train][fun] = 1
#                train = None
#                fun = None
#            elif fun:
#                funs[train] = {fun: 1}
#                train = None
#                fun = None

print("Outputs")
for inputs in outputs:
    print(inputs)
    for fun in outputs[inputs]:
        print(" ", fun, ":", outputs[inputs][fun])

print()
print("Updates")
for inputs in updates:
    print(inputs)
    for fun in updates[inputs]:
        print(" ", fun, ":", updates[inputs][fun])

print()
print("Guards")
for inputs in guards:
    print(inputs)
    for fun in guards[inputs]:
        print(" ", fun, ":", guards[inputs][fun])
