#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jan  3 11:47:57 2022

@author: michael
"""
#    This file is part of EAP.
#
#    EAP is free software: you can redistribute it and/or modify
#    it under the terms of the GNU Lesser General Public License as
#    published by the Free Software Foundation, either version 3 of
#    the License, or (at your option) any later version.
#
#    EAP is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
#    GNU Lesser General Public License for more details.
#
#    You should have received a copy of the GNU Lesser General Public
#    License along with EAP. If not, see <http://www.gnu.org/licenses/>.

import operator
import random
import z3

from deap import algorithms
from deap import base
from deap import creator
from deap import tools
from deap import gp

import pandas as pd
import numpy as np

from itertools import product

from enchant.utils import levenshtein
from numbers import Number

import networkx as nx


# Define new functions
def protectedDiv(left, right):
    if right == 0:
        return float("inf")
    return left / right


def distance_between(expected, actual):
    if actual is None or type(expected) != type(actual):
        return float("inf")
    elif isinstance(expected, Number):
        return abs(expected - actual)
    elif type(expected) == str:
        return levenshtein(expected, actual)
    raise ValueError(f"Expected int, float, or string type, not {type(expected)}.")


def findBestValue(func, args, consts, expected):
    undefined_at = [i for i, x in enumerate(args) if x is None]
    candidates = product(*np.repeat(consts, len(undefined_at)))

    best_val = func(*args) if None not in args else None
    min_distance = (
        distance_between(expected, best_val) if None not in args else float("inf")
    )

    for candidate in candidates:
        args = args.copy()
        for i, c in zip(undefined_at, candidate):
            args[i] = c
        actual = func(*args)
        distance = distance_between(expected, actual)
        if distance < min_distance:
            min_distance = distance
            best_val = actual
    return best_val, min_distance


def evaluate_candidate(individual, points, pset):
    func = gp.compile(expr=individual, pset=pset)
    consts = set(
        [
            item
            for sublist in [set(points[col]) for col in points.columns]
            for item in sublist
            if item is not None
        ]
    )

    values = []
    distances = []
    for row in points.to_records(index=False):
        best_val, min_distance = findBestValue(func, list(row)[:-1], consts, row[-1])
        values.append(best_val)
        distances.append(min_distance)

    return sum(distances)


def fitness(individual, points, pset):
    return evaluate_candidate(individual, points, pset),


def correct(individual, points, pset) -> bool:
    return evaluate_candidate(individual, points, pset) == 0


def setup_pset(points, latentVars):
    pset = gp.PrimitiveSet("MAIN", len(points.columns[:-1]) + len(latentVars))
    #  TODO: Add 0, 1, and 2 here as well.
    pset.addPrimitive(operator.add, 2)
    pset.addPrimitive(operator.sub, 2)
    pset.addPrimitive(operator.mul, 2)
    pset.addPrimitive(protectedDiv, 2, name="div")
    return pset


def run_gp(points: pd.DataFrame, latentVars: [str], pset):
    random.seed(318)

    # Add in the latent variables
    for var in latentVars:
        assert var not in points.columns, f"Latent variable {var} already defined"
        points.insert(0, var, np.repeat(None, len(points)))

    rename = {f"ARG{i}": col for i, col in enumerate(points.columns[:-1])}
    pset.renameArguments(**rename)

    creator.create("FitnessMin", base.Fitness, weights=(-1.0,))
    creator.create("Individual", gp.PrimitiveTree, fitness=creator.FitnessMin)

    toolbox = base.Toolbox()
    toolbox.register("expr", gp.genHalfAndHalf, pset=pset, min_=1, max_=2)
    toolbox.register("individual", tools.initIterate, creator.Individual, toolbox.expr)
    toolbox.register("population", tools.initRepeat, list, toolbox.individual)

    toolbox.register("evaluate", fitness, points=points, pset=pset)

    toolbox.register("select", tools.selTournament, tournsize=2)
    toolbox.register("mate", gp.cxOnePoint)
    toolbox.register("expr_mut", gp.genFull, min_=0, max_=2)
    toolbox.register("mutate", gp.mutUniform, expr=toolbox.expr_mut, pset=pset)

    toolbox.decorate(
        "mate", gp.staticLimit(key=operator.attrgetter("height"), max_value=17)
    )
    toolbox.decorate(
        "mutate", gp.staticLimit(key=operator.attrgetter("height"), max_value=17)
    )

    pop = toolbox.population(n=100)
    hof = tools.HallOfFame(1)

    stats_fit = tools.Statistics(lambda ind: ind.fitness.values)
    stats_size = tools.Statistics(len)
    mstats = tools.MultiStatistics(fitness=stats_fit, size=stats_size)
    mstats.register("avg", np.mean)
    mstats.register("std", np.std)
    mstats.register("min", np.min)
    mstats.register("max", np.max)

    pop, log = algorithms.eaSimple(
        pop, toolbox, 0.5, 0.1, 40, stats=mstats, halloffame=hof, verbose=False
    )
    return hof[0]


def graph(best):
    return gp.graph(best)


def to_z3(T, root, labels, types):
    def _make_tuple(T, root, _parent):
        # Get the neighbors of `root` that are not the parent node. We
        # are guaranteed that `root` is always in `T` by construction.
        children = set(T[root]) - {_parent}
        print(f"Children of {root} = {children}")
        if len(children) == 0:
            return types[labels[root]](labels[root])

        nested = tuple(_make_tuple(T, v, root) for v in children)
        if labels[root] == "add":
            c1, c2 = nested
            return c1 + c2
        elif labels[root] == "sub":
            c1, c2 = nested
            return c1 - c2
        elif labels[root] == "mul":
            c1, c2 = nested
            return c1 * c2
        elif labels[root] == "div":
            c1, c2 = nested
            return c1 / c2
        else:
            raise ValueError(f"Invalid operator {root}")

    # Do some sanity checks on the input.
    if not nx.is_tree(T):
        raise nx.NotATree("provided graph is not a tree")
    if root not in T:
        raise nx.NodeNotFound(f"Graph {T} contains no node {root}")

    return _make_tuple(T, root, None)


if __name__ == "__main__":
    points = pd.read_csv("../../../sample-traces/drinks_coin_obfuscated.csv")
    latentVars = ["r1"]
    pset = setup_pset(points, latentVars)
    best = run_gp(points, latentVars, pset)
    print(best)

    nodes, edges, labels = gp.graph(best)
    g = nx.Graph()
    g.add_nodes_from(nodes)
    g.add_edges_from(edges)
    
    assert nx.is_tree(g), "Expression must be a tree."
    

    generators = {np.dtype("float64"): z3.Real, np.dtype("int64"): z3.Int}

    print(g)
    print(points)
    types = {
        k: generators.get(
            points.dtypes[k], generators[points.dtypes[points.columns[-1]]]
        )
        for k in points
    }
    
    to_z3(g, 0, labels, types=types)
    
    # print(z3.simplify(to_z3(g, 0, labels, types=types)))

    # print(toZ3(g))
