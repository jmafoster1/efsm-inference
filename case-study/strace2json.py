#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jun 24 11:37:56 2019

@author: michael
"""
import json
import os


def make_smaller(i):
    return i
    if i < 100:
        return i
    else:
        return int(make_smaller(i/100))


def num_or_str(a):
    if str(a).isnumeric():
        return make_smaller(a)
    else:
        return str(a)[:10]


def flatten(inputs):
    args = []
    for i in inputs:
        if type(i) == list:
            args += flatten(i)
        elif type(i) == dict:
            args += flatten([v for (k, v) in sorted(i.items())])
        else:
            args.append(i)
    return [num_or_str(a) for a in args]


def is_int(string):
    try:
        int(string)
        return True
    except(ValueError):
        return False


def outputs(string):
    if type(string) == int:
        return [make_smaller(string)]
    string = string.split(" ")
    if len(string) == 0:
        return []
    if is_int(string[0]):
        return [int(string[0]), ' '.join(string[1:])]
    else:
        return [' '.join(string)]


excluded = {'brk', 'mmap'}
for dirName, subdirList, fileList in os.walk('strace-traces'):
    if fileList != []:
        traces = []
        for fileName in fileList:
            with open(os.path.join(dirName, fileName)) as file:
                events = []
                for line in file:
                    syscall = json.loads(line)
                    if syscall['syscall'] not in excluded:
                        events.append({'label': syscall['syscall'],
                                       'inputs': flatten(syscall['args'])[:10],
                                       'outputs': outputs(syscall['result'])})
            traces.append(events)
        command = dirName.split('/')[-1]
        with open('json-traces/'+command+'.json', 'w') as f:
            print(json.dumps(traces, sort_keys=True, indent=2), file=f)
