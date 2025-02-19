# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set
from functools import reduce
from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *
# from code.predicates.syntax import *
# from code.predicates.semantics import *
from logic_utils import fresh_variable_name_generator


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1
    # init stuff that we'll keep
    universe = model.universe
    constant_meanings = model.constant_meanings
    relation_meanings = dict(model.relation_meanings)
    # foreach functions: convert to corresponding relation, add to relation meanings and arities
    for func_name, func_meanings in model.function_meanings.items():
        new_relation_name = function_name_to_relation_name(func_name)
        new_set = set()
        # foreach meaning of function, add that meaning to cor relation's set
        for tup, val in func_meanings.items():
            new_set.add(((val,) + tup))
        relation_meanings[new_relation_name] = new_set
    return Model(universe, constant_meanings, relation_meanings, dict())


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
        # Task 8.2
        # init stuff that we'll keep
        universe = model.universe
        constant_meanings = model.constant_meanings
        relation_meanings = dict()
        function_meanings = dict()
        # foreach relation in old model's relations...
        for relation_name, relation_meaning in model.relation_meanings.items():
            # if original_functions doesnt have cor function: add to relations
            name_as_function = relation_name_to_function_name(relation_name)
            if name_as_function not in original_functions:
                relation_meanings[relation_name] = relation_meaning
                continue
            # else create and add cor function instead
            new_func_dic = dict()
            if len(relation_meaning) >= 1:
                cur_meanings = set()
                i = 0
                for meaning in relation_meaning:
                    i += 1
                    if meaning[1:] not in cur_meanings:
                        # func(x2, x3, ...) = x1
                        new_func_dic[meaning[1:]] = meaning[0]
                        cur_meanings.add(meaning[1:])
                        continue
                    # make sure function wont map same input to different values
                    if new_func_dic[meaning[1:]] != meaning[0]:
                        return None
                # make sure all combos in universe are defined for function
                if i != len(universe) ** len(next(iter(new_func_dic))):
                    return None
            function_meanings[name_as_function] = new_func_dic
        return Model(universe, constant_meanings, relation_meanings, function_meanings)


def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    # Task 8.3

    # for each arg, if its a function create the formula list for it DFS
    formula_list = []
    new_args = []
    for arg in term.arguments:
        if is_function(arg.root):
            formula_list += compile_term(arg)
            updated_name = formula_list[-1].arguments[0]  # assuming what i want is always the last one
            new_args.append(updated_name)
        else:
            new_args.append(arg)

    new_name = next(fresh_variable_name_generator)
    t1 = Term(root=new_name)
    t2 = Term(root=term.root, arguments=new_args)
    new_formula = Formula(root='=', arguments_or_first_or_variable=(t1, t2))

    return formula_list + [new_formula]


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4

    if is_equality(formula.root) or is_relation(formula.root):
        steps = []
        new_relation_args = []
        for arg in formula.arguments:
            # get all steps for this relation
            if is_function(arg.root):
                steps += compile_term(arg)
                new_relation_args.append(steps[-1].arguments[0])
            else:
                new_relation_args.append(arg)

        ret_form0 = Formula(formula.root, new_relation_args)
        for form in reversed(steps):
            # form are of type z1 = f(x,y)
            #  create new relation for form
            brand_new_relation = Formula(function_name_to_relation_name(form.arguments[1].root),
                                         [form.arguments[0]] + list(form.arguments[1].arguments))
            ret_form1 = Formula('->', brand_new_relation, ret_form0)
            ret_form0 = Formula('A', form.arguments[0].root, ret_form1)
        return ret_form0

    if is_unary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first))

    if is_binary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first),
                       replace_functions_with_relations_in_formula(formula.second))

    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))


def replace_functions_with_relations_in_formulas(formulas:
AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    # until now no one promised that f corresponds to F when we changed functions to relations
    # it is true that our model handles it the same way which is why it works with our subsituted models (task1, 2) but
    # now we want it to be true for any model so we add constraints in the form of extra formulas that force the meaning
    # the function f and the relation F to be equal

    all_function_names = reduce(lambda x, y: x | y, [f.functions() for f in formulas])
    new_formulas = {replace_functions_with_relations_in_formula(f) for f in formulas}

    for name, args_num in all_function_names:
        relation_name = function_name_to_relation_name(name)
        var_terms = [Term('x' + str(i)) for i in range(args_num)]
        predicate = Formula('E', 'z', Formula(relation_name, [Term('z')] + var_terms))
        for i in range(args_num):
            predicate = Formula('A', 'x' + str(i), predicate)
        new_formulas.add(predicate)

        f1 = Formula('&', Formula(relation_name, [Term('z1')] + var_terms),
                     Formula(relation_name, [Term('z2')] + var_terms))
        f2 = Formula('=', [Term('z1'), Term('z2')])
        f = Formula('->', f1, f2)
        f = Formula('A', 'z2', f)
        f = Formula('A', 'z1', f)

        for i in range(args_num):
            f = Formula('A', 'x' + str(i), f)
        new_formulas.add(f)

    return new_formulas


def replace_same_helper(formula: Formula):
    if is_relation(formula.root):
        return formula
    if is_equality(formula.root):
        return Formula('SAME', formula.arguments)
    if is_unary(formula.root):
        return Formula(formula.root, replace_same_helper(formula))
    if is_binary(formula.root):
        return Formula(formula.root, replace_same_helper(formula.first), replace_same_helper(formula.second))
    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_same_helper(formula.predicate))


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}
    # Task 8.6
    same = 'SAME'
    all_relations_names = reduce(lambda x, y: x | y, [f.relations() for f in formulas])
    all_formulas = {replace_same_helper(f) for f in formulas}

    # create same properties
    # reflexive:
    x = Term('x')
    y = Term('y')
    z = Term('z')
    ref = Formula('A', 'x', Formula(same, [x, x]))
    sym = Formula('A', 'x', Formula('A', 'y', Formula('->', Formula(same, [x, y]), Formula(same, [y, x]))))
    f1 = Formula('&', Formula(same, [x, y]), Formula(same, [y, z]))
    f2 = Formula(same, [x, z])
    f = Formula('->', f1, f2)
    trans = Formula('A', 'x', Formula('A', 'y', Formula('A', 'z', f)))
    all_formulas = all_formulas | {ref, sym, trans}

    # create formula for each relation name
    for relation_name, args_num in all_relations_names:
        if args_num == 0:
            continue
        var_terms_x = [Term('x' + str(i)) for i in range(args_num)]
        var_terms_y = [Term('y' + str(i)) for i in range(args_num)]

        left_side = Formula(same, [var_terms_x[0], var_terms_y[0]])
        for i in range(1, args_num):
            left_side = Formula('&', Formula(same, [var_terms_x[i], var_terms_y[i]]), left_side)
        right_side = Formula('->', Formula(relation_name, var_terms_x), Formula(relation_name, var_terms_y))
        pred = Formula('->', left_side, right_side)

        for i in range(args_num):
            pred = Formula('A', 'x' + str(i), Formula('A', 'y' + str(i), pred))
        all_formulas.add(pred)

    return all_formulas


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7
    # init the little shits from original model
    universe = model.universe
    constant_meanings = model.constant_meanings
    function_meanings = model.function_meanings
    relation_meanings = dict(model.relation_meanings)
    same_meaning_set = set()
    # define each val in universe is SAME to itself
    for val in universe:
        same_meaning_set.add((val, val))
    relation_meanings['SAME'] = same_meaning_set
    return Model(universe, constant_meanings, relation_meanings, function_meanings)


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8
    # create new universe and learn equivalence classes
    old_universe = set(model.universe)
    new_universe = set()
    equiv_to = dict()
    # for each val in old universe...
    while old_universe:
        # add val to new universe...
        val = old_universe.pop()
        new_universe.add(val)
        # val is in it's own equiv class
        equiv_to[val] = val
        # skip over any other_val that is SAME as val, remember other_val is equiv to val
        for other_val in model.universe:
            if other_val != val and (other_val, val) in model.relation_meanings['SAME']:
                old_universe.remove(other_val)
                equiv_to[other_val] = val
    # create new_constant_meanings
    new_constant_meanings = dict()
    for const, meaning in model.constant_meanings.items():
        new_constant_meanings[const] = equiv_to[meaning]
    # foreach relation, update values in meanings according to appropriate equiv class
    new_relation_meanings = dict()
    for relation, meanings in model.relation_meanings.items():
        # ignore 'SAME' relation, obvs
        if relation == 'SAME':
            continue
        new_relation_meanings[relation] = set()
        for meaning in meanings:
            new_meaning = tuple(x if x in new_universe else equiv_to[x] for x in meaning)
            new_relation_meanings[relation].add(new_meaning)
    return Model(new_universe, new_constant_meanings, new_relation_meanings, model.function_meanings)
