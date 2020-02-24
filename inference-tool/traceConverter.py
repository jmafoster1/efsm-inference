#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Dec 10 13:25:34 2019

@author: michael
"""

import re
import json
import random

root = "/home/michael/Documents/mintframework/mint-inference/src/tests/resources/"
newRoot = "/home/michael/Documents/efsm-inference/inference-tool/experimental-data/"
file = "liftDoors2"
outfile = "liftDoors30"
numTraces = 50

brake = 0
distance = 1
speed = 2
throttle = 3

#desired_outputs = [speed]
#desired_inputs = [brake, distance, speed, throttle]

desired_inputs = [0]
desired_outputs = [0]

obfuscated_inputs = [0]

typeHead = "types\n"


def getTypes(f):
    typeDecl = re.compile("(\w+) +((\w+:[\w\[:\]]+ *)+)")
    typeFun = {'N': lambda x: int(float(x)), 'S': str, 'NI': int, 'I': int}
    types = {}
    line = f.readline().strip()  # Strip off "types"
    line = f.readline().strip()
    global typeHead
    while line != "trace":
        typeHead += line + "\n"
        match = typeDecl.search(line)
        types[match.group(1)] = [typeFun[x.split(":")[1].split("[")[0]] for x in match.group(2).split(" ")]
        line = f.readline().strip()
    return types


def trim(traces, numEvents):
    return [[event for event in trace[:numEvents]] for trace in traces]


def print_original_trace(f, traces):
    print(typeHead, file=f, end="")
    for trace in traces:
        print("trace", file=f)
        for (label, inputs) in trace:
            print(label, " ".join([str(x) for x in inputs]), file=f)


def format_trace(trace):
    labels = [label for label, inputs in trace[:-1]]
    inputs = [inputs for label, inputs in trace[:-1]]
    outputs = [inputs for label, inputs in trace[1:]]
    return [{
            'label': label,
            'inputs': [p for x, p in enumerate(inputs) if x in desired_inputs],
            'outputs': [p for x, p in enumerate(outputs) if x in desired_outputs]
            } for label, inputs, outputs in zip(labels, inputs, outputs)]


def obfuscate_inputs(trace):
    labels = [label for label, inputs in trace[:-1]]
    inputs = [inputs for label, inputs in trace[:-1]]
    outputs = [inputs for label, inputs in trace[1:]]
    return [{
            'label': label,
            'inputs': [n for i, n in enumerate(inputs) if i in desired_inputs and i not in obfuscated_inputs],
            'outputs': [p for x, p in enumerate(outputs) if x in desired_outputs]
            } for label, inputs, outputs in zip(labels, inputs, outputs)]


with open(root+file) as f:
    types = getTypes(f)

    eventRE = re.compile("(\w+) (.*)")

    traces = []
    trace = []

    for line in f.readlines():
        line = line.strip()
        if line == "":
            continue
        if line == "trace":
            if trace != []:
                traces.append(trace)
                trace = []
            continue
        match = eventRE.search(line)
        label = match.group(1)
        inputs = [valueOf(i) for valueOf, i in zip(types[label], match.group(2).split(" "))]
        trace.append((label, inputs))
    traces.append(trace)

traces = [trace for trace in traces if len(trace) >= 5]
traces = random.sample(traces, 2*numTraces)
#traces = trim(traces, 10)

io_traces = [format_trace(t) for t in traces]
obfuscated_traces = [obfuscate_inputs(t) for t in traces]

with open(newRoot+outfile+"-original-train", 'w') as f:
    print_original_trace(f, traces[:numTraces])

with open(newRoot+outfile+"-original-test", 'w') as f:
    print_original_trace(f, traces[numTraces:])

with open(newRoot+outfile+"-train.json", 'w') as f:
    print("[\n" + ",  \n".join(["  [\n    " + ",\n    ".join([json.dumps(event) for event in trace]) + "\n  ]" for trace in io_traces[:numTraces]]) + "\n]", file=f)

with open(newRoot+outfile+"-test.json", 'w') as f:
    print("[\n" + ",  \n".join(["  [\n    " + ",\n    ".join([json.dumps(event) for event in trace]) + "\n  ]" for trace in io_traces[numTraces:]]) + "\n]", file=f)

with open(newRoot+outfile+"-obfuscated-train.json", 'w') as f:
    print("[\n" + ",  \n".join(["  [\n    " + ",\n    ".join([json.dumps(event) for event in trace]) + "\n  ]" for trace in obfuscated_traces[:numTraces]]) + "\n]", file=f)

with open(newRoot+outfile+"-obfuscated-test.json", 'w') as f:
    print("[\n" + ",  \n".join(["  [\n    " + ",\n    ".join([json.dumps(event) for event in trace]) + "\n  ]" for trace in obfuscated_traces[numTraces:]]) + "\n]", file=f)
