# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from functools import reduce
from itertools import product

from propositions.proofs import *

Model = Mapping[str, bool]
BOOL_MAP = {'T': True, 'F': False}
BOOL_MAP_R = {True: 'T', False: 'F'}


def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))

    # base cases
    if is_constant(formula.root):
        return BOOL_MAP[formula.root]

    if is_variable(formula.root):
        return model[formula.root]

    if is_unary(formula.root):  # if it is unary it must have a first
        return not evaluate(formula.first, model)

    if formula.root == '&':
        return evaluate(formula.first, model) and evaluate(formula.second, model)
    if formula.root == '-&':
        return not (evaluate(formula.first, model) and evaluate(formula.second, model))
    if formula.root == '|':
        return evaluate(formula.first, model) or evaluate(formula.second, model)
    if formula.root == '-|':
        return not (evaluate(formula.first, model) or evaluate(formula.second, model))
    if formula.root == '+':
        return (not evaluate(formula.first, model) and evaluate(formula.second, model)) or \
               (evaluate(formula.first, model) and not evaluate(formula.second, model))
    if formula.root == '->':
        return (not evaluate(formula.first, model)) or evaluate(formula.second, model)
    if formula.root == '<->':
        return (evaluate(formula.first, model) and evaluate(formula.second, model)) or\
               (not evaluate(formula.first, model) and not evaluate(formula.second, model))


    raise Exception(formula.root + ' is not Supported')



    # Task 2.1

def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    return (dict(zip(variables, combo)) for combo in product([False, True], repeat=len(variables)))

def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    # Task 2.3
    return (evaluate(formula, m) for m in models)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    s = '|'
    vars = list(sorted(formula.variables()))
    models = all_models(vars)
    for var in vars:
        s += ' '+ var + ' |'
    indexes = [i for i in range(len(s)) if s[i] == '|']
    s += ' ' + str(formula) + ' |'
    indexes.append(len(s)-1)
    print(s)
    for i in range(len(s)):
        if i in indexes:
            print('|', end='')
        else:
            print('-', end='')

    print()

    i, j = 0, 0
    for m in models:
        bools = list(m.values())
        while i < len(s) - len(str(formula)) - 4:
            if i in indexes and j < len(bools):
                print('| ' + BOOL_MAP_R[bools[j]] , end='')
                j += 1
                i += 2
            else:
                print(' ', end='')
            i += 1
        i, j = 0, 0
        print('| ' + BOOL_MAP_R[evaluate(formula, m)], (len(str(formula)) - 2) * ' ', '|')


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    return reduce(lambda x, y: x and y, truth_values(formula, all_models(list(formula.variables()))))
    # Task 2.5a


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    return reduce(lambda x, y: x and y, map(lambda x: not x, truth_values(formula, all_models(list(formula.variables())))))


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    return not is_contradiction(formula)
    # Task 2.5c


def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    model_vars = list(model.keys())
    first = Formula(root=model_vars[0])

    if not model[model_vars[0]]:
        first = Formula(root='~', first=first)

    # if here there are at least 2

    for i in range(1, len(model_vars)):
        cur = Formula(root=model_vars[i])
        if not model[model_vars[i]]:
            cur = Formula(root='~', first=cur)
        first = Formula(root='&', first=first, second=cur)

    return first




    # Task 2.6


def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """

    assert len(variables) > 0
    # only when i need the model to evaluate to true i add a or and the clause that is only true in that case

    bool_list = list(values)
    g = all_models(variables)

    # todo- since i cant return just F for some reason ill return the clause that is always false
    first = Formula(root=variables[0])
    formula = Formula(root='&', first=Formula(root='~', first=first), second=first)
    i = 0
    for model in g:
        if bool_list[i]:
            cur = synthesize_for_model(model)
            formula = Formula(root='|', first=formula, second=cur)

        i += 1

    return formula

    # Task 2.7

# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)
    # Task 4.2
    # so evaluate all assumptions with the given model, if they are all true, return evaluation of conclusion
    return not reduce(lambda x, y: x and y, [evaluate(f, model) for f in rule.assumptions], True) or \
           evaluate(rule.conclusion, model)

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    return reduce(lambda x, y: x and y, [evaluate_inference(rule, model)
                                         for model in all_models(list(rule.variables()))], True)
