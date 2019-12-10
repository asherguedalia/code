# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from logic_utils import frozendict
from propositions.axiomatic_systems import *
from propositions.deduction import *
from propositions.operators import *


def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    return sorted([Formula.parse(k) if model[k] else Formula('~', Formula.parse(k)) for k in model],
                  key=lambda x: str(x)[1:] if str(x)[0] == '~' else str(x))
    # Task 6.1a

def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)

    assumptions = formulae_capturing_model(model)
    # make it ~ formula if evaluation is false
    conclusion = formula
    if not evaluate(formula, model):
        conclusion = Formula(root='~', first=formula)

    statement = InferenceRule(assumptions, conclusion=conclusion)
    rules = AXIOMATIC_SYSTEM

    # base case:
    if is_variable(formula.root):
        first_line = Proof.Line(formula=conclusion)  # justified as an assumption
        return Proof(statement, rules, [first_line])

    elif formula.root == '->':
        if evaluate(formula, model):  # then either φ1 has value False in this model or φ2 has value True in it.
            if not evaluate(formula.first, model):  # then φ1 has value False
                not_fi_1_proof = prove_in_model(formula.first, model)
                # use I2 to prove fi
                idx = len(not_fi_1_proof.lines)
                f = Formula(root='->', first=not_fi_1_proof.statement.conclusion, second=conclusion)
                first_line = Proof.Line(formula=f, rule=I2, assumptions=[])  # idx
                second_line = Proof.Line(formula=conclusion, rule=MP, assumptions=[idx-1, idx])  # idx+1
                return Proof(statement, AXIOMATIC_SYSTEM, list(not_fi_1_proof.lines) + [first_line, second_line])
            else:  # so φ2 has value True in this model
                fi_2_proof = prove_in_model(formula.second, model)
                # use I1 to prove fi
                idx = len(fi_2_proof.lines)
                f = Formula(root='->', first=fi_2_proof.statement.conclusion, second=conclusion)
                first_line = Proof.Line(formula=f, rule=I1, assumptions=[])  # idx
                second_line = Proof.Line(formula=conclusion, rule=MP, assumptions=[idx - 1, idx])  # idx+1
                return Proof(statement, AXIOMATIC_SYSTEM, list(fi_2_proof.lines) + [first_line, second_line])

        else:  # Otherwise, φ has value False in the model, so both φ1 is True and φ2 is False in the model
            fi_1_proof = prove_in_model(formula.first, model)
            not_fi_2_proof = prove_in_model(formula.second, model)
            return combine_proofs(fi_1_proof, not_fi_2_proof, conclusion, NI)

    elif formula.root == '~':
        if evaluate(formula, model):  # If φ evaluates to True, then ψ evaluates to False, so we can recursively prove
                                      # ‘~ψ’ which is exactly φ, as needed.
            not_xsi_proof = prove_in_model(formula.first, model)
            return not_xsi_proof

        else:
            xsi_proof = prove_in_model(formula.first, model)
            idx = len(xsi_proof.lines)
            f = Formula(root='->', first=xsi_proof.statement.conclusion, second=conclusion)  # conclusion is notnotxsi
            first_line = Proof.Line(formula=f, rule=NN, assumptions=[])  # idx
            second_line = Proof.Line(formula=conclusion, rule=MP, assumptions=[idx - 1, idx])  # idx+1
            return Proof(statement, AXIOMATIC_SYSTEM, list(xsi_proof.lines) + [first_line, second_line])

    else:
        # should ever be here
        raise Exception('should not make it here!')

    # Task 6.1b

def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    ant1 = remove_assumption(proof_from_affirmation)
    ant2 = remove_assumption(proof_from_negation)
    conclusion = proof_from_affirmation.statement.conclusion
    new_proof = combine_proofs(ant1, ant2, conclusion, R)
    return new_proof




def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a

    if sorted(model.keys()) == sorted(tautology.variables()):
        # so all variables have been assigned
        return prove_in_model(tautology, model)
    else:  # so there is at least one variable that is not assigned in model
        un_assigned_vars = tautology.variables() - set(list((model.keys())))
        assert len(un_assigned_vars) > 0
        current = list(sorted(un_assigned_vars))[0]
        new_model = dict(model)
        new_model[current] = True
        first_proof = prove_tautology(tautology, new_model)
        new_model[current] = False
        second_proof = prove_tautology(tautology, new_model)
        return reduce_assumption(first_proof, second_proof)

def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    for model in all_models(list(formula.variables())):
        if not evaluate(formula, model):
            return model
    return prove_tautology(formula, {})

    # Task 6.3b

def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    ret_form = rule.conclusion
    for f in reversed(rule.assumptions):
        ret_form = Formula(root='->', first=f, second=ret_form)
    return ret_form

def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b
    rules = AXIOMATIC_SYSTEM

    # prove the tautology
    encoded_formula = encode_as_formula(rule)
    tautology_proof = prove_tautology(encoded_formula, {})
    current_assumptions = list(rule.assumptions)
    lines = list(tautology_proof.lines)
    for f in rule.assumptions:
        cur_idx = len(lines)
        current_assumptions = current_assumptions[1:]  # slice off first assumption
        line_1 = Proof.Line(formula=f)  # justified as assumption  index: cur_idx
        enc = encode_as_formula(InferenceRule(current_assumptions, rule.conclusion))
        line_2 = Proof.Line(formula=enc, rule=MP, assumptions=[cur_idx, cur_idx-1])
        lines += [line_1, line_2]

    return Proof(statement=rule, rules=AXIOMATIC_SYSTEM, lines=lines)



def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})

    all_vars = reduce(lambda x, y: x|y, [f.variables() for f in formulae])
    holds = True
    for model in all_models(list(all_vars)):
        for f in formulae:
            holds = evaluate(f, model) and holds

        if holds:
            return model
        holds = True

    # if we are here there is no model in which they all hold
    assumptions = formulae
    conclusion = Formula.parse('~(p->p)')
    new_rule = InferenceRule(assumptions, conclusion)
    return prove_sound_inference(new_rule)




    # Task 6.5

def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
