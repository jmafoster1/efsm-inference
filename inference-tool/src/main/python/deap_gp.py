#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Jan  3 11:47:57 2022

@author: michael
"""

import operator
import random
import z3
import sys
import traceback

from deap import algorithms
from deap import base
from deap import creator
from deap import tools
from deap import gp

from math import sqrt, isclose

import pandas as pd
import numpy as np

from enchant.utils import levenshtein
from numbers import Number
from itertools import product

import networkx as nx
import logging

logging.basicConfig()

logger = logging.getLogger("main")
logger.setLevel(logging.DEBUG)

creator.create("FitnessMin", base.Fitness, weights=(-1.0,))
creator.create("Individual", gp.PrimitiveTree, fitness=creator.FitnessMin)


def distance_between(expected, actual):
    try:
        if isinstance(expected, Number) and isinstance(actual, Number) and not is_null(actual):
            return abs(expected - actual)
        elif type(expected) == str and type(actual) == str:
            return levenshtein(expected, actual)
        elif type(expected) != type(actual) or is_null(actual):
            return float("inf")
        raise ValueError(f"Expected int, float, or string type, not {actual}:{type(actual)}.")
    except:
        return float("inf")


def rmsd(errors: [float]) -> float:
    assert len(errors) > 0, "Cannot calculate RMSD of empty list."
    total = sum([float(d) ** 2 for d in errors])
    assert not is_null(total), f"sum of {errors} cannot be nan"
    mean = total / len(errors)
    return sqrt(mean)


def is_null(value):
    if isinstance(value, str):
        return value is None
    return value is None or value is pd.NA or np.isnan(value)


def find_smallest_distance(individual, latent_vars, pset, args, expected):
    consts = set()
    type_ = individual[0].ret

    func = gp.compile(expr=individual, pset=pset)

    if not callable(func):
        return distance_between(expected, func)


    if len(latent_vars) == 0:
        actual = func(**args)
        distance = distance_between(expected, actual)
        if isclose(distance, 0, abs_tol=1e-10):
            return 0
        else:
            return distance

    consts = set([c.value for c in pset.terminals[type_] if type(c.value) == type_])
    assignments = [{k: v for k, v in zip(latent_vars, assignment)} for assignment in product(consts, repeat=len(latent_vars))]

    min_distance = float("inf")
    for assignment in assignments:
        new_args = args.copy()
        new_args.update(assignment)
        actual = func(**new_args)
        off_by = distance_between(expected, actual)
        if off_by == 0:
            return 0
        if off_by < min_distance:
            min_distance = off_by

    if isclose(min_distance, 0, abs_tol=1e-10):
        return 0
    assert not is_null(min_distance), "min_distance cannot be nan"
    return min_distance


def vars_in_tree(individual):
    _, _, labels = gp.graph(individual)
    return labels.values()


def latent_variables(individual, points, criterion=lambda points_c: any([is_null(v) for v in points_c])):
    undefined_at = [c for c in list(points) if criterion(points[c])]
    return list(set(undefined_at).intersection(vars_in_tree(individual)))


def all_vars_defined(individual, pset):
    return all([str(v) in pset.mapping for v in vars_in_tree(individual)])


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
    if isinstance(individual, str):
        individual = creator.Individual(
            gp.PrimitiveTree.from_string(individual, pset)
        )

    total_vars = list(points.columns)[:-1]
    latent_vars = [col for col in points if any([is_null(v) for v in points[col]])]
    unused_vars = set(total_vars).difference(vars_in_tree(individual)).difference(latent_vars)

    distances = []
    for inx, row in points.iterrows():
        try:
            best = find_smallest_distance(
                individual, latent_vars, pset, row.iloc[:-1].to_dict(), row[-1]
            )
            distances.append(best)
        except:
            print(f"Problem executing {individual} with arguments\n{row}")
            sys.exit(0)


    assert not any([is_null(x) for x in distances]), "no distance can be nan"

    copy = points.copy()
    copy["distances"] = distances

    mistakes = sum([x > 0 for x in distances])

    assert not is_null(rmsd(distances)), "rmsd(distances) cannot be nan (evaluate_candidate:145)"
    fitness = rmsd(distances) + mistakes

    assert not is_null(fitness), "fitness cannot be nan (evaluate_candidate:148)"

    if len(unused_vars) == 0:
        return fitness
    else:
        return fitness + len(latent_variables(individual, points))


def fitness(individual, points: pd.DataFrame, pset: gp.PrimitiveSet) -> float:
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
    try:
        score = evaluate_candidate(individual, points, pset)
        newline = "\n  "
        assert not is_null(score), f"Score cannot be nan\nPSET:\n  {newline.join(sorted(list(pset.mapping)))}"
        return (score,)
    except:
        # print(f"Problem evaluating candidate {individual}")
        print(traceback.format_exc())
        sys.exit(1)


def correct(individual, points: pd.DataFrame, pset: gp.PrimitiveSet) -> bool:
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

    try:
        latent_vars = latent_variables(individual, points)
        if len(latent_vars) > 0:
            return True

        for _, row in points.iterrows():
            min_distance = find_smallest_distance(
                individual, latent_vars, pset, row.iloc[:-1].to_dict(), row[-1]
            )
            if min_distance > 0:
                return False
        return True
    except:
        print(traceback.format_exc())
        sys.exit(1)


def setup_pset(points: pd.DataFrame) -> gp.PrimitiveSet:
    try:
        return setup_pset_aux(points)
    except:
        print(traceback.format_exc())
        sys.exit(1)


def setup_pset_aux(points: pd.DataFrame) -> gp.PrimitiveSet:
    """
    Set up and return the primitive set. Currently supported operators are +, -, *, and /.

    :param points: The sample function executions with expected outputs.
    N.B. The expected output MUST be the last column in the dataframe.
    N.B. Strings will, by default, appear as objects, so will be indistinguishable from latent registers.
    They MUST be converted explicitly using `.astype('string')` before calling this method.
    :type points: pd.DataFrame
    :return: The primitive set.
    :rtype: gp.PrimitiveSet
    """
    generators = {
        np.dtype("float64"): float,
        np.dtype("int64"): int,
        pd.Int64Dtype(): int,
        pd.StringDtype(): str,
    }
    output_type = generators[points.dtypes[points.columns[-1]]]
    generators[np.dtype("O")] = output_type

    types = points.dtypes.to_dict()
    names = list(types)
    datatypes = [generators[types[v]] for v in names]

    def protectedDiv(left, right):
        if right == 0:
            return float("inf")
        return left / right

    pset = gp.PrimitiveSetTyped("MAIN", datatypes[:-1], output_type)

    rename = {f"ARG{i}": col for i, col in enumerate(names)}
    pset.renameArguments(**rename)

    # Add literal terminals
    for v, typ in zip(names, datatypes):
        if typ == output_type:
            term_set = set(points[v])
            for term in term_set:
                if not is_null(term):
                    pset.addTerminal(term, typ)

    if output_type == str:
        pset.addTerminal("", str)
        # pset.addPrimitive(lambda x: x, [str], str, name="id")
    elif output_type == float:
        pset.addTerminal(0.0, float)
        pset.addTerminal(1.0, float)
        pset.addTerminal(2.0, float)
        pset.addPrimitive(operator.add, [float, float], float)
        pset.addPrimitive(operator.sub, [float, float], float)
        pset.addPrimitive(operator.mul, [float, float], float)
        pset.addPrimitive(protectedDiv, [float, float], float, name="div")
    elif output_type == int:
        pset.addTerminal(0, int)
        pset.addTerminal(1, int)
        pset.addTerminal(2, int)
        pset.addPrimitive(operator.add, [int, int], int)
        pset.addPrimitive(operator.sub, [int, int], int)
        pset.addPrimitive(operator.mul, [int, int], int)
    elif output_type == bool:
        pset.addTerminal(True, bool)
        pset.addTerminal(False, bool)
        pset.addPrimitive(operator.__and__, [bool, bool], bool)
        pset.addPrimitive(operator.__or__, [bool, bool], bool)
        pset.addPrimitive(operator.__not__, [bool, bool], bool)
    else:
        raise ValueError(f"Invalid output type {output_type}.")
    return pset


def choose_terminal(pset, type_, prob=0.7):
    variables = [t for t in pset.terminals[type_] if t.name.startswith("ARG")]
    constants = [t for t in pset.terminals[type_] if t not in variables]
    if random.random() < prob and variables != []:
        return random.choice(variables)
    else:
        return random.choice(constants)


def mutateByTerminal(individual, pset):
    if len(individual) < 2:
        return (individual,)

    index = random.randrange(1, len(individual))
    node = individual[index]
    slice_ = individual.searchSubtree(index)
    term = choose_terminal(pset, node.ret)

    if gp.isclass(term):
        term = term()
    individual[slice_] = [term]

    return (individual,)


def mutateByCommute(individual, pset):
    if len(individual) < 2:
        return (individual,)

    possible_nodes = [(i, node) for i, node in enumerate(individual) if node.arity > 1]
    if len(possible_nodes) == 0:
        return (individual,)
    i, node = random.choice(possible_nodes)
    individual[i].args.reverse()
    return (individual,)


def mutateByFuzz(individual, pset):
    terminals = [(i, node) for i, node in enumerate(individual) if node.arity == 0]

    index, node = random.choice(terminals)

    term = random.choice(pset.terminals[node.ret])
    if gp.isclass(term):
        term = term()
    individual[index] = term

    return (individual,)


def mutInsert(individual, pset):
    """Inserts a new branch at a random position in *individual*. The subtree
    at the chosen position is used as child node of the created subtree, in
    that way, it is really an insertion rather than a replacement. Note that
    the original subtree will become one of the children of the new primitive
    inserted, but not perforce the first (its position is randomly selected if
    the new primitive has more than one child).

    :param individual: The normal or typed tree to be mutated.
    :returns: A tuple of one tree.
    """
    index = random.randrange(len(individual))
    node = individual[index]
    slice_ = individual.searchSubtree(index)
    choice = random.choice

    # As we want to keep the current node as children of the new one,
    # it must accept the return value of the current node
    primitives = [p for p in pset.primitives[node.ret] if node.ret in p.args]

    if len(primitives) == 0:
        return (individual,)

    new_node = choice(primitives)
    new_subtree = [None] * len(new_node.args)
    position = choice([i for i, a in enumerate(new_node.args) if a == node.ret])

    for i, arg_type in enumerate(new_node.args):
        if i != position:
            term = choose_terminal(pset, arg_type)
            if gp.isclass(term):
                term = term()
            new_subtree[i] = term

    new_subtree[position: position + 1] = individual[slice_]
    new_subtree.insert(0, new_node)
    individual[slice_] = new_subtree
    return (individual,)


def mutate(individual, pset, MAX_MUTATIONS=3):
    mutations = 0
    newNode = creator.Individual(gp.PrimitiveTree.from_string(str(individual), pset))
    mutate = True
    while mutate and mutations < MAX_MUTATIONS:
        mutations += 1
        mutate = random.choice([True, False])
        if len(individual) < 2:
            newNode = mutInsert(newNode, pset)[0]
            continue

        op = random.choice(range(6))
        if op == 0:
            # HVL SUB
            newNode = gp.mutNodeReplacement(newNode, pset)[0]
            # logger.debug("Mutating", individual, "by substitution", newNode)
        if op == 1:
            # HLV DEL
            newNode = gp.mutShrink(newNode)[0]
            # logger.debug("Mutating", individual, "by deletion", newNode)
        if op == 2:
            # HVL INS
            newNode = mutInsert(newNode, pset)[0]
            # logger.debug("Mutating", individual, "by insertion", newNode)
        if op == 3:
            # Reverse this.children if they have the same return type, e.g. (x - y) -> (y - x)
            newNode = mutateByCommute(newNode, pset)[0]
            # logger.debug("Mutating", individual, "by commutation", newNode)
        if op == 4:
            # mutate by replacing a random node with a terminal
            newNode = mutateByTerminal(newNode, pset)[0]
            # logger.debug("Mutating", individual, "by terminal swap", newNode)
        if op == 5:
            # fuzz a terminal
            newNode = mutateByFuzz(newNode, pset)[0]
            # logger.debug("Mutating", individual, "by fuzzing", newNode)
    return (newNode,)


def gen_terminal(expr, pset, type_):
    try:
        term = choose_terminal(pset, type_)
    except IndexError:
        _, _, traceback = sys.exc_info()
        raise IndexError(
            "The gp.generate function tried to add "
            "a terminal of type '%s', but there is "
            "none available." % (type_,)
        ).with_traceback(traceback)
    if gp.isclass(term):
        term = term()
    expr.append(term)


def gen_primitive(expr, pset, type_, stack, depth):
    try:
        prim = random.choice(pset.primitives[type_])
        expr.append(prim)
        for arg in reversed(prim.args):
            stack.append((depth + 1, arg))
    except IndexError:
        gen_terminal(expr, pset, type_)


def generate(pset, min_, max_, condition, type_=None):
    """Generate a Tree as a list of list. The tree is build
    from the root to the leaves, and it stop growing when the
    condition is fulfilled.

    :param pset: Primitive set from which primitives are selected.
    :param min_: Minimum height of the produced trees.
    :param max_: Maximum Height of the produced trees.
    :param condition: The condition is a function that takes two arguments,
                      the height of the tree to build and the current
                      depth in the tree.
    :param type_: The type that should return the tree when called, when
                  :obj:`None` (default) the type of :pset: (pset.ret)
                  is assumed.
    :returns: A grown tree with leaves at possibly different depths
              depending on the condition function.
    """
    if type_ is None:
        type_ = pset.ret
    expr = []
    height = random.randint(min_, max_)
    stack = [(0, type_)]
    while len(stack) != 0:
        depth, type_ = stack.pop()
        if condition(height, depth):
            gen_terminal(expr, pset, type_)
        else:
            gen_primitive(expr, pset, type_, stack, depth)
    return expr


def genHalfAndHalf(pset, min_, max_, type_=None):
    """Generate an expression with a PrimitiveSet *pset*.
    Half the time, the expression is generated with :func:`~deap.gp.genGrow`,
    the other half, the expression is generated with :func:`~deap.gp.genFull`.

    :param pset: Primitive set from which primitives are selected.
    :param min_: Minimum height of the produced trees.
    :param max_: Maximum Height of the produced trees.
    :param type_: The type that should return the tree when called, when
                  :obj:`None` (default) the type of :pset: (pset.ret)
                  is assumed.
    :returns: Either, a full or a grown tree.
    """

    def genGrow(height, depth):
        """Expression generation stops when the depth is equal to height
        or when it is randomly determined that a node should be a terminal.
        """
        return depth == height or (
            depth >= min_ and random.random() < pset.terminalRatio
        )

    def genFull(height, depth):
        """Expression generation stops when the depth is equal to height."""
        return depth == height

    return generate(
        pset, min_, max_, condition=random.choice([genGrow, genFull]), type_=type_
    )


def is_distinct(pop):
    seen = []
    for p in pop:
        if p in seen:
            return False
        else:
            seen.append(p)
    return True


def parsimony_select(individuals, k):
    return sorted(
        individuals, key=operator.attrgetter("fitness", "height"), reverse=True
    )[:k]


def run_gp(
    points: pd.DataFrame, pset, mu=100, lamb=10, ngen=100, random_seed=0, seeds=[]
):
    points = points.replace({np.nan: None, np.NaN: None})
    random.seed(random_seed)

    toolbox = base.Toolbox()
    toolbox.register("expr", genHalfAndHalf, pset=pset, min_=0, max_=4)
    toolbox.register("individual", tools.initIterate, creator.Individual, toolbox.expr)
    toolbox.register("population", tools.initRepeat, list, toolbox.individual)

    toolbox.register("evaluate", fitness, points=points, pset=pset)

    generators = {
        np.dtype("float64"): z3.Real,
        np.dtype("int64"): z3.Int,
        pd.Int64Dtype(): z3.Int,
        pd.StringDtype(): z3.String,
    }

    types = {
        k: generators.get(
            points.dtypes[k], generators[points.dtypes[points.columns[-1]]]
        )
        for k in points
    }
    toolbox.register("simplify", simplify, pset=pset, types=types)
    toolbox.register("select", parsimony_select)
    toolbox.register("mate", gp.cxOnePoint)
    toolbox.register("expr_mut", gp.genFull, min_=0, max_=2)
    toolbox.register("mutate", mutate, pset=pset)

    toolbox.decorate(
        "mate", gp.staticLimit(key=operator.attrgetter("height"), max_value=17)
    )
    toolbox.decorate(
        "mutate", gp.staticLimit(key=operator.attrgetter("height"), max_value=17)
    )

    pop = toolbox.population(n=mu)
    assert len(pop) == mu, f"Unexpected generated population size: {len(pop)} != {mu}."

    if len(seeds) > 0:
        print("SEEDS!")
        for seed in seeds:
            print("Trying to add", seed)
            try:
                individual = creator.Individual(
                    gp.PrimitiveTree.from_string(seed, pset)
                )
                print(f"Fitness of {individual} is {fitness(individual, points, pset)}")
                if fitness(individual, points, pset) == (0,):
                    print("Found perfect individual!")
                    return simplify(individual, pset, types)
                pop.append(individual)
            except TypeError:
                print(f"Failed to add seed {seed}")
                # print("Type error.")
                print(traceback.format_exc())
                # sys.exit(1)
                # print(pset.mapping)
                # assert False
                # pass

    for terms in pset.terminals.values():
        terms = [creator.Individual([i]) for i in terms]
        for t in terms:
            if t not in pop:
                pop.append(t)
    pop = make_distinct(pop)
    assert is_distinct(pop), "Population contains duplicated individuals."
    pop += toolbox.population(n=mu - len(pop))
    pop = sorted(pop, key=lambda x: x.fitness.values)

    hof = tools.HallOfFame(1)

    stats_fit = tools.Statistics(lambda ind: ind.fitness.values)
    stats_size = tools.Statistics(len)
    mstats = tools.MultiStatistics(fitness=stats_fit, size=stats_size)
    mstats.register("avg", np.mean)
    mstats.register("std", np.std)
    mstats.register("min", np.min)
    mstats.register("max", np.max)

    pop, log = eaMuPlusLambda(
        pop,
        toolbox,
        mu,
        lamb,
        0.5,
        0.1,
        ngen,
        stats=mstats,
        halloffame=hof,
        verbose=False,
    )

    return simplify(hof[0], pset, types)


def graph(best) -> ([int], [(int, int)], {int: str}):
    (nodes, edges, labels) = gp.graph(best)
    return (nodes, edges, {k: str(v) for k, v in labels.items()})


def get_types(points: pd.DataFrame) -> {str: str}:
    type_strings = {
        np.dtype("float64"): "Real",
        np.dtype("int64"): "Int",
        pd.Int64Dtype(): "Int",
        pd.StringDtype(): "String",
    }
    output_type = type_strings[points.dtypes[points.columns[-1]]]
    type_strings[np.dtype("O")] = output_type
    return {v: type_strings[t] for v, t in points.dtypes.iteritems()}


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

    try:
        z3_exp = to_z3(g, 0, labels, types)
        if type(z3_exp) in {int, float, str}:
            return creator.Individual(gp.PrimitiveTree([gp.Terminal(z3_exp)]))
        return creator.Individual(from_z3(z3.simplify(z3_exp), pset))
    except z3.Z3Exception:
        return individual
    except TypeError:
        return individual


def fill_pop(more, individual, avoid=[], TIMEOUT=3):
    fillers = []
    for _ in range(more):
        fillers.append(individual())
    return fillers


def make_distinct(pop):
    new_pop = []
    for ind in pop:
        if ind not in new_pop:
            new_pop.append(ind)
    assert is_distinct(new_pop)
    return new_pop


def eaMuPlusLambda(
    population,
    toolbox,
    mu,
    lambda_,
    cxpb,
    mutpb,
    ngen,
    stats=None,
    halloffame=None,
    verbose=__debug__,
):
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
    logbook.header = ["gen", "nevals"] + (stats.fields if stats else [])

    # population = make_distinct(population, mu, toolbox.individual)
    # population += fill_pop(mu - len(population), toolbox.individual, population)
    # assert (
    #     len(population) == mu
    # ), f"Population should contain {mu} individuals but contains {len(population)}."

    # Evaluate the individuals with an invalid fitness
    invalid_ind = [ind for ind in population if not ind.fitness.valid]
    fitnesses = list(toolbox.map(toolbox.evaluate, invalid_ind))
    for ind, fit in zip(invalid_ind, fitnesses):
        ind.fitness.values = fit
    population[:] = toolbox.select(population, mu)

    if halloffame is not None:
        halloffame.update(population)

    record = stats.compile(population) if stats is not None else {}
    logbook.record(gen=0, nevals=len(invalid_ind), **record)
    if verbose:
        logger.debug(logbook.stream)

    # Begin the generational process
    for gen in range(1, ngen + 1):
        seen = {}
        for p in population:
            p = str(p)
            if p not in seen:
                seen[p] = 0
            seen[p] += 1

        if halloffame[0].fitness.values[0] == 0:
            return population, logbook

        # Vary the population
        offspring = algorithms.varOr(population, toolbox, lambda_, cxpb, mutpb)

        population += offspring
        population = [toolbox.simplify(i) for i in population]
        population = make_distinct(population)
        assert is_distinct(population), "Population contains duplicates"
        population += toolbox.population(n=mu - len(population))

        # Evaluate the individuals with an invalid fitness
        invalid_ind = [ind for ind in offspring if not ind.fitness.valid]
        fitnesses = toolbox.map(toolbox.evaluate, invalid_ind)
        for ind, fit in zip(invalid_ind, fitnesses):
            ind.fitness.values = fit

        # Update the hall of fame with the generated individuals
        if halloffame is not None:
            halloffame.update(offspring)

        # Select the next generation population
        population = sorted(population, key=lambda i: i.fitness.values)[:mu]
        assert (
            len(population) == mu
        ), f"Population should contain {mu} individuals but contains {len(population)}."
        # Update the statistics with the new population
        # record = stats.compile(population) if stats is not None else {}
        logbook.record(gen=gen, nevals=len(invalid_ind), **record)
        if verbose:
            logger.debug(logbook.stream)

    return population, logbook


def from_string(string, pset):
    return gp.PrimitiveTree.from_string(string, pset)


def need_latent(points: pd.DataFrame) -> bool:
    inputs = list(points.columns)[:-1]
    if len(set(points.iloc[:, -1])) <= 1:
        return False
    if inputs == [] and len(set(points.iloc[:, -1])) > 1:
        return True
    elif points.dtypes[list(points.columns)[-1]] == float:
        for _, group in points.groupby(inputs):
            outputs = group.iloc[:, -1]
            for o1 in outputs:
                for o2 in outputs:
                    if not isclose(o1, o2, abs_tol=1e-10):
                        return True
        return False
    else:
        return any(
            [len(set(group.iloc[:, -1])) > 1 for _, group in points.groupby(inputs)]
        )


def shortcut_latent(points: pd.DataFrame) -> bool:
    return len(points.columns[:-1]) == 0 and len(set(points[points.columns[-1]])) > 1


if __name__ == "__main__":
    points = pd.read_csv("../../../sample-traces/scanette.csv")

    for col in points:
        if points.dtypes[col] == object:
            points[col] = points[col].astype("string")
        # if points.dtypes[col] == np.int64:
        #     points[col] = points[col].astype("float")
    # logger.info(f"\n{points}")
    # points["perfect"] = points["i0"] - points["i1"]
    # logger.info(f"\n{points}")
    # logger.info(points.dtypes)
    # assert False

    latentVars = []
    # latentVars.append("r1")
    for var in latentVars:
        assert var not in points.columns, f"Latent variable {var} already defined"
        points.insert(0, var, None)

    pset = setup_pset(points)

    # ind = gp.PrimitiveTree.from_string("sub(i0, i1)", pset)
    # logger.info(f"Fitness of {ind} is {fitness(ind, points, pset)}")
    # assert False

    best = run_gp(points, pset, random_seed=7, seeds=["sub(i0, r1)"])
    logger.info(f"best is {best}")
    logger.info(graph(best))

    for s in range(20):
        best = run_gp(points, pset, random_seed=s, ngen=200)
        corr = correct(best, points, pset)
        if corr:
            logger.info(f"Gen {s} best {best}")
        else:
            logger.info(f"Gen {s} incorrect {best}: {fitness(best, points, pset)}")

    logger.info(points)
    logger.info(f"best is {best}")
    logger.info(f"correct? {correct(best, points, pset)}")

    expected = points.columns[-1]

    logger.info(f"exected type {points.dtypes[expected]}")

    generators = {
        np.dtype("float64"): z3.Real,
        np.dtype("int64"): z3.Int,
        pd.Int64Dtype(): z3.Int,
        pd.StringDtype(): z3.String,
    }
    logger.info(generators)

    types = {
        k: generators.get(points.dtypes[k], generators[points.dtypes[expected]])
        for k in points
    }

    simplified = simplify(best, pset, types)
    logger.info(simplified)
    logger.info(correct(simplified, points, pset))
    logger.info(get_types(points))
