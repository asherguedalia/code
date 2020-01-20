# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

# from code.predicates.syntax import *
# from code.predicates.proofs import *
# from code.predicates.prover import *

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for first-order predicate logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1
    if is_equality(formula.root) or is_relation(formula.root):
        return True
    if is_quantifier(formula.root):
        return False
    if is_unary(formula.root):
        return is_quantifier_free(formula.first)
    if is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    raise Exception('Duuddee not cool')


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2
    if is_quantifier_free(formula):
        return True

    # otherwise we have a quantifier
    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)

    # otherwise it has a quantifier not at the top so bad
    return False


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.5
    def uniquely_rename_quantified_variables(formula: Formula) -> \
            Tuple[Formula, Proof]:
        """Converts the given formula to an equivalent formula with uniquely named
        variables, and proves the equivalence of these two formulas.

        Parameters:
            formula: formula to convert, which contains no variable names starting
                with ``z``.

        Returns:
            A pair. The first element of the pair is a formula equivalent to the
            given formula, with the exact same structure but with the additional
            property of having uniquely named variables, obtained by consistently
            replacing each variable name that is bound in the given formula with a
            new variable name obtained by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
            second element of the pair is a proof of the equivalence of the given
            formula and the returned formula (i.e., a proof of
            `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
            via `~predicates.prover.Prover.AXIOMS` and
            `ADDITIONAL_QUANTIFICATION_AXIOMS`.
        """
        # Task 11.5
        prover = Prover(set(ADDITIONAL_QUANTIFICATION_AXIOMS) | set(Prover.AXIOMS), False)

        # base case
        if is_relation(formula.root) or is_equality(formula.root):
            # so nothing to convert
            formula_to_prove = equivalence_of(formula, formula)
            step1 = prover.add_tautology(Formula('->', formula, formula))  # skeleton i assume is of form p -> p
            step2 = prover.add_tautology(Formula('->', formula, formula))
            step3 = prover.add_tautological_implication(formula_to_prove, {step1, step2})
            return formula, prover.qed()

        if is_quantifier(formula.root):
            new_var_name = next(fresh_variable_name_generator)
            sub_map = {formula.variable: Term(new_var_name)}

            subbed_vars_predicate, p1 = uniquely_rename_quantified_variables(formula.predicate)
            step1 = prover.add_proof(p1.conclusion, p1)
            my_map = {'R': formula.predicate.substitute({formula.variable: Term('_')}, set()),
                      'Q': subbed_vars_predicate.substitute({formula.variable: Term('_')}, set()),
                      'x': formula.variable, 'y': new_var_name}

            new_formula = Formula(formula.root, new_var_name, subbed_vars_predicate.substitute(sub_map, set()))
            formula_to_prove = equivalence_of(formula, new_formula)

            idx_map = {'A': 14, 'E': 15}

            step1 = prover.add_proof(p1.conclusion, p1)
            step2 = prover.add_instantiated_assumption(Formula('->', p1.conclusion, formula_to_prove),
                                                       ADDITIONAL_QUANTIFICATION_AXIOMS[idx_map[formula.root]], my_map)
            step3 = prover.add_mp(formula_to_prove, step1, step2)
            return new_formula, prover.qed()


def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    # if isn't quantifier --> just add tautology
    if not is_quantifier(formula.first.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    first_var = formula.first.variable
    # negate the first predicate, prove
    not_first_pred = Formula('~', formula.first.predicate)
    pred, proof = pull_out_quantifications_across_negation(not_first_pred)
    change_quant_proof = prover.add_proof(proof.conclusion, proof)

    # create new form: change quant -> equivalence of preds
    new_quant = 'E' if formula.first.root == 'A' else 'A'
    change_quant_not_pred = Formula(new_quant, first_var, not_first_pred)
    change_quant_pred = Formula(new_quant, first_var, pred)
    conc_then_equiv = Formula("->", proof.conclusion,
                              equivalence_of(change_quant_not_pred, change_quant_pred))
    # start adding to proof
    # create sub map for first assump
    first_sub_map = {'R': str(not_first_pred.substitute({first_var: Term('_')})),
                     'Q': str(pred.substitute({first_var: Term('_')})),
                     'x': first_var,
                     'y': first_var}
    first_ass_index = prover.add_instantiated_assumption(conc_then_equiv,
                                                         ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                             14 if new_quant == "A" else 15],
                                                         first_sub_map)
    mp_index = prover.add_mp(equivalence_of(change_quant_not_pred, change_quant_pred), change_quant_proof,
                             first_ass_index)
    # create sub map for second assump
    second_sub_map = {'R': str(formula.first.predicate.substitute({first_var: Term("_")})),
                      "x": first_var}
    form_equiv_not_pred = equivalence_of(formula, change_quant_not_pred)
    second_ass_index = prover.add_instantiated_assumption(form_equiv_not_pred,
                                                          ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                              0 if new_quant == 'E' else 1],
                                                          second_sub_map)
    # add final equivalence
    prover.add_tautological_implication(equivalence_of(formula, change_quant_pred), [mp_index, second_ass_index])
    return change_quant_pred, prover.qed()


def pull_out_quantifications_from_left_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    # if isn't quantifier --> just add tautology
    if not is_quantifier(formula.first.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    # init shits
    first_var = formula.first.variable
    first_pred = formula.first.predicate
    first_quant = formula.first.root
    no_pred = Formula(formula.root, first_pred, formula.second)
    pred, proof = pull_out_quantifications_from_left_across_binary_operator(no_pred)
    # prove quant update
    update_quant_proof = prover.add_proof(proof.conclusion, proof)
    # get quant and axiom
    axiom_num, first_quant = get_quant_and_axiom_task_7_1(formula.root, first_quant)
    # start adding to proof
    conc_then_equiv = Formula('->', proof.conclusion,
                              equivalence_of(Formula(first_quant, first_var, no_pred),
                                             Formula(first_quant, first_var, pred)))
    # create sub map for first assump
    first_sub_map = {'R': str(no_pred.substitute({first_var: Term('_')})),
                     'Q': str(pred.substitute({first_var: Term('_')})), 'x': first_var,
                     'y': first_var}
    fist_ass_index = prover.add_instantiated_assumption(conc_then_equiv,
                                                        ADDITIONAL_QUANTIFICATION_AXIOMS[
                                                            14 if first_quant == 'A' else 15],
                                                        first_sub_map)
    mp_index = prover.add_mp(equivalence_of(Formula(first_quant, first_var, no_pred),
                                            Formula(first_quant, first_var, pred)), update_quant_proof,
                             fist_ass_index)
    # create sub map for second assump
    second_sub_map = {'R': str(first_pred.substitute({first_var: Term('_')})),
                      'x': first_var, 'Q': str(formula.second)}
    form_equiv_no_pred = equivalence_of(formula, Formula(first_quant, first_var, no_pred))
    second_ass_index = prover.add_instantiated_assumption(form_equiv_no_pred,
                                                          ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_num], second_sub_map)
    # add final equivalence
    prover.add_tautological_implication(equivalence_of(formula, Formula(first_quant, first_var, pred)),
                                        [mp_index, second_ass_index])
    return Formula(first_quant, first_var, pred), prover.qed()


def get_quant_and_axiom_task_7_1(root, quant):
    # should never return -1, just for debugging
    # axiom_num = -1
    # if op is '->' --> switch quantifier, get appropriate axiom
    if root == '->':
        if quant == 'A':
            quant = 'E'
            axiom_num = 10
        else:
            quant = 'A'
            axiom_num = 11
    # elif '&' or '|' --> keep quant just update axiom
    elif root == '|':
        if quant == 'A':
            axiom_num = 6
        else:
            axiom_num = 7
    else:
        if quant == 'A':
            axiom_num = 2
        else:
            axiom_num = 3
    return axiom_num, quant


def pull_out_quantifications_from_right_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    # if isn't quantifier --> just add tautology
    if not is_quantifier(formula.second.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    # init shits
    quant = formula.second.root
    second_pred = formula.second.predicate
    second_var = formula.second.variable
    axiom_num = get_axiom_task_7_2(formula.root, quant)
    no_pred = Formula(formula.root, formula.first, second_pred)
    pred, proof = pull_out_quantifications_from_right_across_binary_operator(no_pred)
    # start adding to proof
    update_conc_proof = prover.add_proof(proof.conclusion, proof)
    conc_then_equiv = Formula("->", proof.conclusion, equivalence_of(Formula(quant, second_var, no_pred),
                                                                     Formula(quant, second_var, pred)))
    first_sub_map = {'R': str(no_pred.substitute({second_var: Term("_")})),
                     'Q': str(pred.substitute({second_var: Term("_")})), "x": second_var, "y": second_var}

    first_ass_index = prover.add_instantiated_assumption(conc_then_equiv,
                                                         ADDITIONAL_QUANTIFICATION_AXIOMS[14 if quant == "A" else 15],
                                                         first_sub_map)

    mp_index = prover.add_mp(equivalence_of(Formula(quant, second_var, no_pred),
                                            Formula(quant, second_var, pred)), update_conc_proof, first_ass_index)

    second_sub_map = {'R': str(second_pred.substitute({formula.second.variable: Term("_")})), "x": second_var,
                      "Q": str(formula.first)}
    form_no_pred = equivalence_of(formula, Formula(quant, second_var, no_pred))
    second_ass_index = prover.add_instantiated_assumption(form_no_pred,
                                                          ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_num], second_sub_map)

    prover.add_tautological_implication(equivalence_of(formula, Formula(quant, second_var, pred)),
                                        [mp_index, second_ass_index])

    return Formula(quant, second_var, pred), prover.qed()


def get_axiom_task_7_2(root, quant):
    if root == '->':
        return 12 if quant == 'A' else 13
    elif root == '|':
        return 8 if quant == 'A' else 9
    else:
        return 4 if quant == 'A' else 5


def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8


def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.10
