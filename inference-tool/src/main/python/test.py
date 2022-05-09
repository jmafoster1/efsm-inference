#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Apr 29 08:13:14 2022

@author: michael
"""
from deap import gp
from deap import creator
from deap import base

import operator
import networkx as nx
import z3

creator.create("FitnessMin", base.Fitness, weights=(-1.0,))
creator.create("Individual", gp.PrimitiveTree, fitness=creator.FitnessMin)


def to_z3(tree, labels, types):
    def _make_tuple(tree, root, _parent):
        # Get the neighbors of `root` that are not the parent node. We
        # are guaranteed that `root` is always in `tree` by construction.
        children = set(tree[root]) - {_parent}
        if len(children) == 0:
            if labels[root] in types:
                return types[labels[root]](labels[root])
            else:
                return labels[root]

        nested = tuple(_make_tuple(tree, v, root) for v in children)
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
            try:
                return c1 / c2
            except ZeroDivisionError:
                return float("inf")
        elif labels[root] == "id":
            return nested[0]
        else:
            raise ValueError(f"Invalid operator {root}")

    # Do some sanity checks on the input.
    root = 0  # By construction of GP individuals
    if not nx.is_tree(tree):
        raise nx.NotATree("provided graph is not a tree")
    if root not in tree:
        raise nx.NodeNotFound(f"Graph {tree} contains no node {root}")

    return _make_tuple(tree, root, None)


def make_binary(fun, children):
    if len(children) == 2:
        c1 = to_exp_string(children[0])
        c2 = to_exp_string(children[1])
        return f"{fun}({c1}, {c2})"
    else:
        c1 = to_exp_string(children[0])
        c2 = make_binary(fun, children[1:])
        return f"{fun}({c1}, {c2})"


def to_exp_string(exp):
    if str(exp.decl()) == "+":
        return make_binary("add", exp.children())
    elif str(exp.decl()) == "-":
        return make_binary("sub", exp.children())
    elif str(exp.decl()) == "*":
        return make_binary("mul", exp.children())
    elif str(exp.decl()) == "/":
        return make_binary("div", exp.children())
    elif type(exp) == z3.RatNumRef:
        x2 = exp.as_fraction()
        return str(float(x2.numerator) / float(x2.denominator))
    else:
        return str(exp)


def from_z3(exp, pset):
    return gp.PrimitiveTree.from_string(to_exp_string(exp), pset)


def simplify(individual, pset, types):
    # Duplicate the individual
    individual = creator.Individual(gp.PrimitiveTree.from_string(str(individual), pset))
    nodes, edges, labels = gp.graph(individual)
    g = nx.Graph()
    g.add_nodes_from(nodes)
    g.add_edges_from(edges)

    z3_exp = to_z3(g, labels, types)
    print(z3_exp)
    if type(z3_exp) in {int, float, str}:
        return creator.Individual(gp.PrimitiveTree([gp.Terminal(z3_exp)]))
    return creator.Individual(from_z3(z3.simplify(z3_exp), pset))


pset = gp.PrimitiveSetTyped("MAIN", [int], int)
pset.renameArguments(ARG0="r1")
pset.addPrimitive(operator.add, [int, int], int)
pset.addPrimitive(operator.sub, [int, int], int)
pset.addPrimitive(operator.mul, [int, int], int)

seed = "add(mul(0, 0), sub(r1, 50))"
exp = gp.PrimitiveTree.from_string(seed, pset)
simplified = simplify(exp, pset, {'r1': z3.Int})
print(simplified)
