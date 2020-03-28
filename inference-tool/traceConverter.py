#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Dec 10 13:25:34 2019

@author: michael
"""

import re
import json
import random

root = "/home/michael/eclipse-workspace/concurrency/"
#root = "/home/michael/Documents/ICSMEData/"

newRoot = "/home/michael/Documents/efsm-inference/inference-tool/experimental-data/"

numTraces = 30

file = "all.log"
#file = "liftDoors2"

outfile = "spaceInvaders"
#outfile = "liftDoors-2-"

outfile += str(numTraces)

x = 0
shields = 1
aliens = 2
time = 0


desired_inputs = {
    "start": [x, aliens, shields],
    "stop": [x, aliens, shields],
    "alienHit": [aliens],
    "addAlien": [],
    "moveWest": [x],
    "moveEast": [x],
    "launchMissile": [],
    "shieldHit": [shields],
    "win": [],
    "lose": [],
    
    "setTimer": [time],
    "waitTimer": [time],
    "fullyOpen": [time],
    "fullyClosed": [time],
    "systemInitReady": [time],
    "closingDoor": [time],
    "buttonInterrupted": [time],
    "openingDoor": [time],
    "timeout": [time],
    "requestOpen": [time]

}

desired_outputs = desired_inputs


def varname(obj, namespace=globals()):
    return [name for name in namespace if namespace[name] is obj][0]


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


typeHead = "types\n"


def print_original_trace(f, traces):
    print(typeHead, file=f, end="")
    for trace in traces:
        print("trace", file=f)
        for (label, inputs) in trace:
            print(label, " ".join([str(p) for x, p in enumerate(inputs) if x in desired_inputs[label]]), file=f)


def format_trace(trace):
    labels = [label for label, inputs in trace[:-1]]
    inputs = [inputs for label, inputs in trace[:-1]]
    outputs = [inputs for label, inputs in trace[1:]]
    return [{
            'label': label,
            'inputs': [p for x, p in enumerate(inputs) if x in desired_inputs[label]],
            'outputs': [p for x, p in enumerate(outputs) if x in desired_outputs[label]]
            } for label, inputs, outputs in zip(labels, inputs, outputs)]


def obfuscate_inputs(trace, obfuscated_inputs):
    labels = [label for label, inputs in trace[:-1]]
    inputs = [inputs for label, inputs in trace[:-1]]
    outputs = [inputs for label, inputs in trace[1:]]
    return [{
            'label': label,
            'inputs': [n for i, n in enumerate(inputs) if i in desired_inputs[label] and i not in obfuscated_inputs],
            'outputs': [p for x, p in enumerate(outputs) if x in desired_outputs[label]]
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
print(len(traces), "traces in total")

traces = random.sample(traces, 2*numTraces)

io_traces = [format_trace(t) for t in traces]

with open(newRoot+outfile+"-original-train", 'w') as f:
    print_original_trace(f, traces[:numTraces])

with open(newRoot+outfile+"-original-test", 'w') as f:
    print_original_trace(f, traces[numTraces:])

with open(newRoot+outfile+"-train.json", 'w') as f:
    print("[\n" + ",  \n".join(["  [\n    " + ",\n    ".join([json.dumps(event) for event in trace]) + "\n  ]" for trace in io_traces[:numTraces]]) + "\n]", file=f)

with open(newRoot+outfile+"-test.json", 'w') as f:
    print("[\n" + ",  \n".join(["  [\n    " + ",\n    ".join([json.dumps(event) for event in trace]) + "\n  ]" for trace in io_traces[numTraces:]]) + "\n]", file=f)

outfiles = set([f"{outfile}"])

for var in [item for sublist in desired_outputs.values() for item in sublist]:
    outfiles.add(f"{outfile}-obfuscated-{varname(var)}")
    obfuscated_traces = [obfuscate_inputs(t, [var]) for t in traces]
    
    with open(newRoot+outfile+f"-obfuscated-{varname(var)}-train.json", 'w') as f:
        print("[\n" + ",  \n".join(["  [\n    " + ",\n    ".join([json.dumps(event) for event in trace]) + "\n  ]" for trace in obfuscated_traces[:numTraces]]) + "\n]", file=f)
    
    with open(newRoot+outfile+f"-obfuscated-{varname(var)}-test.json", 'w') as f:
        print("[\n" + ",  \n".join(["  [\n    " + ",\n    ".join([json.dumps(event) for event in trace]) + "\n  ]" for trace in obfuscated_traces[numTraces:]]) + "\n]", file=f)

preprocessors = ["gp", "none"]

for p in preprocessors:
    for file in outfiles:
        with open(newRoot+file+f"-{p}-submissions.sh", 'w') as f:
            for i in range(30):
                print(f"sbatch bessemer-run.sh {random.randint(10000, 99999)} {random.randint(10000, 99999)} {random.randint(10000, 99999)} {file} {p}", file=f)
