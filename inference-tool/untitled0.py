#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Dec 13 11:53:20 2019

@author: michael
"""

import re

root = "/home/michael/Documents/efsm-inference/inference-tool/dotfiles/"
file = "log"

merge = "Trying to merge Nata\((\d+)\) and Nata\((\d+)\) - "
failureRE = re.compile(merge + "Failed")
successRE = re.compile(merge + "Success")

failures = {}
successes = {}

with open(root+file) as log:
    for line in log:
        failure = failureRE.search(line)
        success = successRE.search(line)
        
        if failure:
            merge = (int(failure.group(1)), int(failure.group(2)))
            if merge in failures:
                failures[merge] += 1
            else:
                failures[merge] = 1
        elif success:
            merge = (int(success.group(1)), int(success.group(2)))
            if merge in successes:
                successes[merge] += 1
            else:
                successes[merge] = 1

print("failures:", failures)
print("successes: ", successes)

print("intersection: ", set(failures.keys()).intersection(set(successes.keys())))