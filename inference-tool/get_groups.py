#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Oct 20 13:14:41 2023

@author: michael
"""

import networkx as nx
import pandas as pd
import re
import deap_gp
import json

class AdditiveDict():
    def __init__(self, generator):
        self.generator = generator
        self.data = {}


    def __getitem__(self, key):
        if key not in self.data:
            self.data[key] = self.generator(self.data)
        return self.data[key]

def to_dot(efsm, filepath, highlight = None):
    highlight = [] if highlight is None else highlight
    G = nx.MultiDiGraph(name="NewBB_19states")
    for origin in efsm:
        for ip in efsm[origin]:
            for config in efsm[origin][ip]:
                (tid, dest, op) = efsm[origin][ip][config]
                color = "red" if (origin, dest, ip, op) in highlight else "black"
                G.add_edge(origin, dest, label=f"{ip}/{op}", configuration=config, color=color)
    nx.nx_pydot.write_dot(G, filepath)
    return G

def to_json(efsm, filepath, pset, initial_state, initial_configuration, output_funs=None, rk={}):
    output_funs = [] if output_funs is None else output_funs
    sk = AdditiveDict(lambda x: len(x))
    sk[None]
    G = []
    for origin in efsm:
        for ip in efsm[origin]:
            for config in efsm[origin][ip]:
                (tid, dest, op) = efsm[origin][ip][config]
                ip_sig, _, ip_val = event_re.match(ip).groups()
                op_sig, _, op_val = event_re.match(op).groups()
                updates = []
                if ip_val is not None:
                    updates.append([rk[f"r_{ip_sig}"], deap_gp.to_nodes_edges_labels("i0", pset, rk)])
                ip_val = [] if ip_val is None else [int(ip_val)]
                outputs = [f'"{op_sig}"']
                guards = [deap_gp.to_nodes_edges_labels(f"eq(i{i}, {v})", pset, rk) for i, v in enumerate(ip_val)]
                if op_val is not None:
                    if (origin, dest, ip_sig, op_sig) in output_funs:
                        aexp = str(output_funs[(origin, dest, ip_sig, op_sig)])
                        outputs.append(aexp)
                        updates.append([rk[f"r_{op_sig}"], deap_gp.to_nodes_edges_labels(aexp, pset, rk)])
                    else:
                        outputs.append(op_val)
                        updates.append([rk[f"r_{op_sig}"], deap_gp.to_nodes_edges_labels(op_val, pset)])
                outputs = [deap_gp.to_nodes_edges_labels(p, pset, rk) for p in outputs]
                transition = {
                                "tid": [tid],
                                "origin": int(sk[origin]), 
                                "dest": int(sk[dest]), 
                                "label":ip_sig, 
                                "arity":len(ip_val),
                                "guards":guards,
                                "outputs":outputs,
                                "updates":updates,
                                "drop_guards": (origin, dest, ip_sig, op_sig) in output_funs
                             }
                new = True
                for t_prime in G:
                    if {k:v for k, v in t_prime.items() if k != "tid"} == transition:
                        print("FOUND DUPLICATE")
                        G.append(transition | {"tid": [tid]+t_prime["tid"]})
                        new = False
                        break
                if new:
                    G.append(transition | {"tid": [tid]})
    G.append(
        {
            "tid": [0],
            "origin": sk[None], 
            "dest": sk[initial_state], 
            "label":"INIT", 
            "arity":0,
            "guards":[],
            "outputs":[deap_gp.to_nodes_edges_labels("INIT", pset)],
            "updates":[(rk[k], deap_gp.to_nodes_edges_labels(v, pset, rk)) for k, v in initial_configuration.items()],
            "drop_guards": False
        }
    )
    with open(filepath, 'w') as f:
        json.dump(G, f, indent=2)
    print(sk.data)
    return G
                
    

event_re = re.compile(r"(\w+)(\((\w+)\))?")

conjecture = nx.nx_pydot.read_dot("new_BB_19states_sampled_configb.dot")

trace = pd.read_csv("trace.csv")
trace = trace[["Step", "Input", "Output", "ra", "rb", "rA"]]
trace["Step"] = trace["Step"].astype(int)
for r in ["ra", "rb", "rA"]:
    trace[r] = [1] + trace[r][:-1].tolist()
    trace[r] = trace[r].astype(int)

efsm = {}

for tid, (origin, dest, data) in enumerate(conjecture.edges(data=True), 1):
    label = data["label"][1:-1]
    config = data["configuration"][1:-1]
    ip, op = label.split("/")
    if origin not in efsm:
        efsm[origin] = {}
    if ip not in efsm[origin]:
        efsm[origin][ip] = {}
    assert config not in efsm[origin][ip], f"Already observed configuration {config}"
    efsm[origin][ip][config] = (tid, dest, op)

initial_state = "BB"
current_state = initial_state
observation = []
for inx, event in trace.iloc[2:].iterrows():
    origin = current_state
    step, ip, op, ra, rb, rA = event
    print(step, f"{ip}/{op}")
    observed = True
    ip_sig, _, ip_val = event_re.match(ip).groups()
    ip_val = int(ip_val) if ip_val is not None else None
    try:
        tid, current_state, observed_op = efsm[origin][ip][f"[{ra},{rb},{rA}]"]
    except KeyError:
        observed = False
        poss_steps = [efsm[origin][ip][cfg] for cfg in efsm[origin][ip]]
        assert len(poss_steps) == 1, f"Bad possible steps: {poss_steps}"
        tid, current_state, observed_op = poss_steps[0]
    # to_dot(efsm, f"steps/step_{step}.dot", highlight=[(origin, current_state, ip, op)])
    assert observed_op == op, f"Bad output {step}: {origin} --> {current_state} {ip}/{op} != {ip}/{observed_op}\n{efsm[origin]}\n{poss_steps}"
    # if observed_op != op:
        # print(f"Bad output {step}: {origin} --> {current_state} {ip}/{op} != {ip}/{observed_op}\n{efsm[origin]}\n{poss_steps}")
    op_sig, _, op_val = event_re.match(observed_op).groups()
    op_val = int(op_val) if op_val is not None else None
    observation.append(
            {
                "origin": origin,
                "dest": current_state,
                "ip_sig": ip_sig, 
                "i0": ip_val, 
                "op_sig": op_sig, 
                "op_arg": op_val,
                "r_a": ra,
                "r_b": rb,
                "r_A": rA,
                "TID": tid,
                "observed": observed,
                "matches": observed_op == op
            }
        )
            

with open("trace.json", 'w') as f:
    observation = [{'origin': None, 'dest': initial_state, 'ip_sig': 'INIT', 'i0': None, 'op_sig': 'INIT', 'op_arg': None, 'r_a': None, 'r_b': None, 'r_A': None, 'TID': 0, 'observed': False}] + observation
    json.dump([[{"label": event['ip_sig'], "inputs": [event['i0']] if event['i0'] is not None else [], "outputs": [x for x in [event['op_sig'], event['op_arg']] if x is not None]} for event in observation[:600]]], f, indent=2)

observation = pd.DataFrame(observation).dropna()
permission = 'w'
output_funs = {}
for tid, group in observation.groupby(["origin", "dest", "ip_sig", "op_sig"]):
    group = group[["i0", "r_a", "r_b", "op_arg"]].astype(int)
    # print(group)
    pset = deap_gp.setup_pset(group)
    best = deap_gp.run_gp(
        group,
        pset,
        random_seed=3,
        latent_vars_rows=[() for i in range(len(group))],
        seeds=["mul(i0, r_b)"]
    )
    correct = deap_gp.correct(best, group, pset, [() for i in range(len(group))])
    with open("log", permission) as f:
        print("RESULT", tid, len(group), best, correct, file=f)
        if not correct:
            print(group, file=f)
        permission='a'
    if correct:
        output_funs[tid] = best # deap_gp.to_z3_string(best, group.dtypes)
    # break


#%%
full_pset = deap_gp.setup_full_pset(observation[["i0", "r_a", "r_b", "r_A", "op_arg"]])
full_pset.addTerminal("INIT")
rk = {"r_a": "r1", "r_b": "r2", "r_A": "r3"}
initial_configuration = {"r_a": "0", "r_b": "0", "r_A": "0"}
converted = to_json(efsm, "generalised.json", full_pset, initial_state, initial_configuration, output_funs, rk)
for t in converted:
    print(t)
