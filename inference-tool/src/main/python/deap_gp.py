#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jan  3 11:47:57 2022

@author: michael
"""

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

from enchant.utils import levenshtein
from numbers import Number

import networkx as nx


def distance_between(expected, actual):
    if actual is None or type(expected) != type(actual):
        return float("inf")
    elif isinstance(expected, Number):
        return abs(expected - actual)
    elif type(expected) == str:
        return levenshtein(expected, actual)
    raise ValueError(f"Expected int, float, or string type, not {type(expected)}.")


def find_smallest_distance(individual, pset, args, consts, expected):
    func = gp.compile(expr=individual, pset=pset)

    if type(individual) in {int, float, str}:
        return distance_between(expected, func)

    undefined_at = [i for i, x in args.items() if x is None]

    _, _, labels = gp.graph(individual)
    vars_in_tree = labels.values()
    latent_vars = set(undefined_at).intersection(vars_in_tree)

    min_distance = float("inf")

    if len(latent_vars) == 0:
        return distance_between(expected, func(**args)) if None not in args else float("inf")

    for var in latent_vars:
        for value in consts:
            new_args = args.copy()
            new_args[var] = value
            actual = func(**new_args)
            off_by = distance_between(expected, actual)
            if off_by < min_distance:
                min_distance = off_by
    return min_distance


def evaluate_candidate(
    individual, points: pd.DataFrame, pset: gp.PrimitiveSet
) -> float:
    """
    Evaluate a candidate function for a set of function executions and aggregate the distances between the expected
    and actual values.

    :param individual: The candidate function to be evaluated.
    :type individual: TYPE
    :param points: The points with which to evaluate the individual.
    N.B. The expected output MUST be the last column in the table.
    :type points: pd.DataFrame
    :param pset: The set of primitives.
    :type pset: TYPE
    :return: The aggregated distance between expected and actual values.
    :rtype: float
    """
    consts = set(
        [
            item
            for sublist in [set(points[col]) for col in points.columns]
            for item in sublist
            if item is not None
        ]
    )

    distances = []
    for _, row in points.iterrows():
        min_distance = find_smallest_distance(individual, pset, row.iloc[:-1].to_dict(), consts, row[-1])
        distances.append(min_distance)

    return sum(distances)


def fitness(
    individual, points: pd.DataFrame, pset: gp.PrimitiveSet
) -> float:
    """
    Determine the fitness of an individual based on its ability to account for a set of expected function executions.

    :param individual: The candidate function to be evaluated.
    :type individual: TYPE
    :param points: The points with which to evaluate the individual.
    N.B. The expected output MUST be the last column in the table.
    :type points: pd.DataFrame
    :param pset: The set of primitives.
    :type pset: TYPE
    :return: The fitness of the individnal.
    :rtype: float
    """
    return (evaluate_candidate(individual, points, pset),)


def correct(
    individual, points: pd.DataFrame, pset: gp.PrimitiveSet
) -> bool:
    """
    Does the candidate function perfectly reproduce the expected executions, assuming any latent variables hold the
    correct values upon evaluation?

    :param individual: The candidate function to be evaluated.
    :type individual: TYPE
    :param points: The points with which to evaluate the individual.
    N.B. The expected output MUST be the last column in the table.
    :type points: pd.DataFrame
    :param pset: The set of primitives.
    :type pset: TYPE
    :return: The fitness of the individnal.
    :rtype: bool
    """
    return evaluate_candidate(individual, points, pset) == 0


def setup_pset(points: pd.DataFrame) -> gp.PrimitiveSet:
    """
    Set up and return the primitive set. Currently supported operators are +, -, *, and /.

    :param points: The sample function executions with expected outputs.
    N.B. The expected output MUST be the last column in the dataframe.
    :type points: pd.DataFrame
    :param latentVars: A list of latent variable names.
    :type latentVars: [str]
    :return: The primitive set.
    :rtype: gp.PrimitiveSet
    """
    types = points.dtypes.iloc[:-1].to_dict()
    names = list(types)
    generators = {np.dtype("float64"): float, np.dtype("int64"): int, pd.StringDtype(): str}
    output_type = generators[points.dtypes[points.columns[-1]]]
    generators[np.dtype('O')] = output_type

    datatypes = [generators[types[v]] for v in names]

    def protectedDiv(left, right):
        if right == 0:
            return float("inf")
        return left / right
    
    
    pset = gp.PrimitiveSetTyped("MAIN", datatypes, output_type)

    rename = {f"ARG{i}": col for i, col in enumerate(names)}
    pset.renameArguments(**rename)

    pset.addTerminal(0, int)
    pset.addTerminal(1, int)
    pset.addTerminal(2, int)
    pset.addTerminal(0, float)
    pset.addTerminal(1, float)
    pset.addTerminal(2, float)
    pset.addTerminal("", str)
    pset.addTerminal(True, bool)
    pset.addTerminal(False, bool)

    pset.addPrimitive(operator.add, [str,str], str)
    pset.addPrimitive(operator.add, [float,float], float)
    pset.addPrimitive(operator.sub, [float,float], float)
    pset.addPrimitive(operator.mul, [float,float], float)
    pset.addPrimitive(protectedDiv, [float,float], float)
    pset.addPrimitive(operator.add, [int,int], int)
    pset.addPrimitive(operator.sub, [int,int], int)
    pset.addPrimitive(operator.mul, [int,int], int)
    pset.addPrimitive(protectedDiv, [int,int], int)
    return pset


def run_gp(points: pd.DataFrame, pset, mu=100, lamb=10, random_seed=0):
    random.seed(random_seed)

    creator.create("FitnessMin", base.Fitness, weights=(-1.0,))
    creator.create("Individual", gp.PrimitiveTree, fitness=creator.FitnessMin)

    toolbox = base.Toolbox()
    toolbox.register("expr", gp.genHalfAndHalf, pset=pset, min_=0, max_=2)
    toolbox.register("individual", tools.initIterate, creator.Individual, toolbox.expr)
    toolbox.register("population", tools.initRepeat, list, toolbox.individual)

    toolbox.register("evaluate", fitness, points=points, pset=pset)

    generators = {np.dtype("float64"): z3.Real, np.dtype("int64"): z3.Int, pd.StringDtype(): z3.String}

    types = {
        k: generators.get(
            points.dtypes[k], generators[points.dtypes[points.columns[-1]]]
        )
        for k in points
    }
    toolbox.register("simplify", simplify, pset=pset, types=types)

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
    


    pop, log = algorithms.eaMuPlusLambda(
        pop, toolbox, mu, lamb, 0.5, 0.1, 40, stats=mstats, halloffame=hof, verbose=False
    )
    return hof[0]


def graph(best):
    return gp.graph(best)


def get_types(points: pd.DataFrame) -> {str: str}:
    type_strings = {np.dtype("int64"): "Int", np.dtype("float64"): "Real", pd.StringDtype(): "String", np.dtype("O"): "String"}
    return {v: type_strings[t] for v, t in points.dtypes.iteritems()}


def to_z3(T, root, labels, types):
    def _make_tuple(T, root, _parent):
        # Get the neighbors of `root` that are not the parent node. We
        # are guaranteed that `root` is always in `T` by construction.
        children = set(T[root]) - {_parent}
        if len(children) == 0:
            if labels[root] in types:
                return types[labels[root]](labels[root])
            else:
                return labels[root]

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
            try:
                return c1 / c2
            except ZeroDivisionError:
                return float("inf")
        else:
            raise ValueError(f"Invalid operator {root}")

    # Do some sanity checks on the input.
    if not nx.is_tree(T):
        raise nx.NotATree("provided graph is not a tree")
    if root not in T:
        raise nx.NodeNotFound(f"Graph {T} contains no node {root}")

    return _make_tuple(T, root, None)

def from_z3(exp, pset):
    return gp.PrimitiveTree.from_string(str(exp), pset)


def simplify(individual, pset, types):
    nodes, edges, labels = gp.graph(best)
    g = nx.Graph()
    g.add_nodes_from(nodes)
    g.add_edges_from(edges)

    assert nx.is_tree(g), "Expression must be a tree."
    z3_exp = to_z3(g, 0, labels, types)
    if type(z3_exp) in {int, float, str}:
        return z3_exp
    return from_z3(z3.simplify(z3_exp), pset)


def eaMuPlusLambda(population, toolbox, mu, lambda_, cxpb, mutpb, ngen,
                   stats=None, halloffame=None, verbose=__debug__):
    r"""This is the :math:`(\mu + \lambda)` evolutionary algorithm.
    :param population: A list of individuals.
    :param toolbox: A :class:`~deap.base.Toolbox` that contains the evolution
                    operators.
    :param mu: The number of individuals to select for the next generation.
    :param lambda\_: The number of children to produce at each generation.
    :param cxpb: The probability that an offspring is produced by crossover.
    :param mutpb: The probability that an offspring is produced by mutation.
    :param ngen: The number of generation.
    :param stats: A :class:`~deap.tools.Statistics` object that is updated
                  inplace, optional.
    :param halloffame: A :class:`~deap.tools.HallOfFame` object that will
                       contain the best individuals, optional.
    :param verbose: Whether or not to log the statistics.
    :returns: The final population
    :returns: A class:`~deap.tools.Logbook` with the statistics of the
              evolution.
    The algorithm takes in a population and evolves it in place using the
    :func:`varOr` function. It returns the optimized population and a
    :class:`~deap.tools.Logbook` with the statistics of the evolution. The
    logbook will contain the generation number, the number of evaluations for
    each generation and the statistics if a :class:`~deap.tools.Statistics` is
    given as argument. The *cxpb* and *mutpb* arguments are passed to the
    :func:`varOr` function. The pseudocode goes as follow ::
        evaluate(population)
        for g in range(ngen):
            offspring = varOr(population, toolbox, lambda_, cxpb, mutpb)
            evaluate(offspring)
            population = select(population + offspring, mu)
    First, the individuals having an invalid fitness are evaluated. Second,
    the evolutionary loop begins by producing *lambda_* offspring from the
    population, the offspring are generated by the :func:`varOr` function. The
    offspring are then evaluated and the next generation population is
    selected from both the offspring **and** the population. Finally, when
    *ngen* generations are done, the algorithm returns a tuple with the final
    population and a :class:`~deap.tools.Logbook` of the evolution.
    This function expects :meth:`toolbox.mate`, :meth:`toolbox.mutate`,
    :meth:`toolbox.select` and :meth:`toolbox.evaluate` aliases to be
    registered in the toolbox. This algorithm uses the :func:`varOr`
    variation.
    """
    logbook = tools.Logbook()
    logbook.header = ['gen', 'nevals'] + (stats.fields if stats else [])

    # Evaluate the individuals with an invalid fitness
    invalid_ind = [ind for ind in population if not ind.fitness.valid]
    fitnesses = toolbox.map(toolbox.evaluate, invalid_ind)
    for ind, fit in zip(invalid_ind, fitnesses):
        ind.fitness.values = fit

    if halloffame is not None:
        halloffame.update(population)

    record = stats.compile(population) if stats is not None else {}
    logbook.record(gen=0, nevals=len(invalid_ind), **record)
    if verbose:
        print(logbook.stream)

    # Begin the generational process
    for gen in range(1, ngen + 1):
        # Vary the population
        offspring = algorithms.varOr(population, toolbox, lambda_, cxpb, mutpb)

        # Evaluate the individuals with an invalid fitness
        invalid_ind = [ind for ind in offspring if not ind.fitness.valid]
        fitnesses = toolbox.map(toolbox.evaluate, invalid_ind)
        for ind, fit in zip(invalid_ind, fitnesses):
            ind.fitness.values = fit

        # Update the hall of fame with the generated individuals
        if halloffame is not None:
            halloffame.update(offspring)

        # Select the next generation population
        population[:] = toolbox.select(population + offspring, mu)
        population = [toolbox.simplify(individual) for individual in population]

        # Update the statistics with the new population
        record = stats.compile(population) if stats is not None else {}
        logbook.record(gen=gen, nevals=len(invalid_ind), **record)
        if verbose:
            print(logbook.stream)

    return population, logbook


if __name__ == "__main__":
    points = pd.read_csv("../../../sample-traces/drinks_select_obfuscated.csv")
    for col in points:
        if points.dtypes[col] == object:
            points[col] = points[col].astype("string")

    latentVars = ["r1"]
    for var in latentVars:
        assert var not in points.columns, f"Latent variable {var} already defined"
        points.insert(0, var, None)

    pset = setup_pset(points)
    best = run_gp(points, pset, random_seed=10)
    print(points)
    print("best is", best)
    print("correct?", correct(best, points, pset))

    expected = points.columns[-1]

    print("exected type", points.dtypes[expected])

    generators = {np.dtype("float64"): z3.Real, np.dtype("int64"): z3.Int, pd.StringDtype(): z3.String}
    print(generators)

    types = {
        k: generators.get(
            points.dtypes[k], generators[points.dtypes[expected]]
        )
        for k in points
    }

    simplified = simplify(best, pset, types)
    print(simplified)
    print(correct(simplified, points, pset))

    # print(get_types(points, np.float64))
    # print(toZ3(g))
