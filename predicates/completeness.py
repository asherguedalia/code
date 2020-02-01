# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/completeness.py

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *
from itertools import product


# from code.predicates.syntax import *
# from code.predicates.semantics import *
# from code.predicates.proofs import *
# from code.predicates.prover import *
# from code.predicates.deduction import *
# from code.predicates.prenex import *

def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants


def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)


def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation, is one of
        the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.1
    # for every n ary relation:
    # get all relation names

    relations = set()
    for sentence in sentences:
        relations.update(sentence.relations())

    constants = get_constants(sentences)
    for relation_name, num_args in relations:
        for combo in product(constants, repeat=num_args):
            # check if one of the sentances or its negation is relation_name(combo)
            f = Formula(relation_name, combo)
            not_f = Formula('~', f)
            if f not in sentences and not_f not in sentences:
                return False

    return True


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.2
    constants = get_constants(sentences)
    for sentence in sentences:

        if sentence.root == 'A':
            variable = sentence.variable
            for const in constants:
                f = sentence.predicate.substitute({variable: Term(const)}, set())
                # now we need to see if f is in sentences as any part
                if f not in sentences:
                    return False
    return True


def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences, ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.3
    constants = get_constants(sentences)
    for sentence in sentences:
        if sentence.root == 'E':
            ans = False
            variable = sentence.variable
            for const in constants:
                f = sentence.predicate.substitute({variable: Term(const)}, set())
                # now we need to see if f is in sentences as any part
                if f in sentences:
                    ans = True
            if not ans:
                return False

    return True


def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.
    
    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2

    # its in prenex normal form and all bound variables so lets start instatiaitonto find a formula
    # that is not satisfied

    if not is_quantifier(unsatisfied.root):
        # so it itself is a legal answer
        return unsatisfied

    # if here so it is quantified
    for c in model.universe:
        pred = unsatisfied.predicate.substitute({unsatisfied.variable: Term(c)}, set())
        if not model.evaluate_formula(pred) and pred in sentences:
            # otherwise it is satisfied so nothing to look into or its is not in sentences in that case it was an
            # existential quantifier so only one instantiation needed to be
            # in this case because it is closed set it has to also have somewhere this formula in a way thats not
            # satisfied
            return find_unsatisfied_quantifier_free_sentence(sentences, model, pred)


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # Task 12.3.1
    if is_relation(quantifier_free.root) or is_equality(quantifier_free.root):
        return {quantifier_free}
    if is_unary(quantifier_free.root):
        return get_primitives(quantifier_free.first)
    if is_binary(quantifier_free.root):
        return get_primitives(quantifier_free.first) | get_primitives(quantifier_free.second)
    raise Exception('i mean where the *** should i really even start')


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)

    # Task 12.3.2
    constants = get_constants(sentences)
    constant_meanings = {k: k for k in constants}
    relation_meanings = {}
    for sentence in sentences:
        if is_relation(sentence.root):
            if sentence.root in relation_meanings:
                relation_meanings[sentence.root].add(tuple([str(x) for x in sentence.arguments]))
            else:
                relation_meanings[sentence.root] = {tuple([str(x) for x in sentence.arguments])}
        if is_unary(sentence.root):
            if is_relation(sentence.first.root):
                # so for now i understand to do nothing in this part but if something dont work id look into it here
                pass
    model = Model(universe=constants, constant_meanings=constant_meanings,
                  relation_meanings=relation_meanings, function_meanings={})

    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            # so its inconsistent
            quantifier_free = find_unsatisfied_quantifier_free_sentence(sentences, model, sentence)
            primitive_sentences = get_primitives(quantifier_free)
            prover = Prover(set(Prover.AXIOMS) | sentences, False)
            step0 = prover.add_assumption(quantifier_free)
            steps = {step0}
            for f in primitive_sentences:
                # add f or its negation whichever one is in sentences
                if f in sentences:
                    steps.add(prover.add_assumption(f))
                else:
                    assert Formula('~', f) in sentences  # maybe im creating a ~~ sitution, in that case check for it
                    steps.add(prover.add_assumption(Formula('~', f)))
            contradiction = Formula('&', quantifier_free, Formula('~', quantifier_free))
            prover.add_tautological_implication(contradiction, steps)
            return prover.qed()
    return model


def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4
    # init shits
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    new_conclusion = proof_from_negation.conclusion
    # prove negated assumption
    affirmed_assumption = list(proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    prove_negation = proof_by_way_of_contradiction(proof_from_affirmation, affirmed_assumption.formula)
    new_lines = list(prove_negation.lines)
    # prove conc using negated-assumption-proof
    negation_form = prove_negation.conclusion
    num_lines_in_other = len(new_lines)
    neg_form_line_num = -1
    for i, line in enumerate(proof_from_negation.lines):
        new_line = line_to_new_line(line, i, num_lines_in_other, negation_form, neg_form_line_num)
        if type(new_line) == int:
            # num_lines_in_other -= 1
            neg_form_line_num = i
            continue
        new_lines.append(new_line)
    return Proof(common_assumptions, new_conclusion, new_lines)


def line_to_new_line(line, line_num, num_lines_in_other, negation_form, neg_form_line_num):
    if type(line) == Proof.UGLine:
        pred_line_num = get_line_num(line.predicate_line_number, num_lines_in_other, neg_form_line_num)
        new_line = Proof.UGLine(line.formula, pred_line_num)
    elif type(line) == Proof.MPLine:
        ant_line_num = get_line_num(line.antecedent_line_number, num_lines_in_other, neg_form_line_num)
        cond_line_num = get_line_num(line.conditional_line_number, num_lines_in_other, neg_form_line_num)
        new_line = Proof.MPLine(line.formula, ant_line_num, cond_line_num)
    elif type(line) == Proof.TautologyLine:
        new_line = line
    elif type(line) == Proof.AssumptionLine:
        if line.formula == negation_form:
            return line_num
        else:
            new_line = line
    return new_line


def get_line_num(line_num, num_lines_in_other, neg_form_line_num):
    if neg_form_line_num == -1:
        return line_num + num_lines_in_other
    if line_num == neg_form_line_num:
        return num_lines_in_other - 1
    if line_num < neg_form_line_num:
        return line_num + num_lines_in_other
    else:  # line_num > neg_form_line
        return line_num + num_lines_in_other - 1


def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5


def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6


def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: a valid proof.
        constant: a constant name that does not appear as a template constant
            name in any of the assumptions of the given proof.
        variable: a variable name that does not appear anywhere in given the
            proof or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7.1


def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()
    # Task 12.7.2


def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8
