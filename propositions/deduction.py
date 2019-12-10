# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    new_rules = {MP} | antecedent_proof.rules | {conditional}
    new_statement = InferenceRule(assumptions=antecedent_proof.statement.assumptions, conclusion=consequent)

    f = Formula(root='->', first=antecedent_proof.statement.conclusion, second=consequent)
    new_lines = list(antecedent_proof.lines)
    count = len(new_lines)
    extra_line1 = Proof.Line(formula=f, rule=conditional, assumptions=[])
    extra_line2 = Proof.Line(formula=consequent, rule=MP, assumptions=[count-1, count])
    new_lines += [extra_line1, extra_line2]
    return Proof(statement=new_statement, rules=new_rules, lines=new_lines)



def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules

    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)

    new_rules = {MP} | antecedent1_proof.rules | {double_conditional}
    new_statement = InferenceRule(assumptions=antecedent1_proof.statement.assumptions, conclusion=consequent)

    f = Formula(root='->', first=antecedent2_proof.statement.conclusion, second=consequent)
    f2 = Formula(root='->', first=antecedent1_proof.statement.conclusion, second=f)
    new_lines = list(antecedent1_proof.lines)
    count = len(new_lines)
    extra_line1 = Proof.Line(formula=f2, rule=double_conditional, assumptions=[])  # count
    extra_line2 = Proof.Line(formula=f, rule=MP, assumptions=[count - 1, count])  # count + 1
    # need to update indexes here
    extra_proof_lines = [Proof.Line(l.formula, l.rule, list(map(
        lambda x: x+count+2, l.assumptions))) if not l.is_assumption() else l for l in antecedent2_proof.lines]


    new_lines = new_lines + [extra_line1, extra_line2] + extra_proof_lines
    new_count = len(new_lines)
    assert new_lines[new_count - 1].formula == antecedent2_proof.statement.conclusion
    extra_line3 = Proof.Line(formula=consequent, rule=MP, assumptions=[new_count - 1, count + 1])  # new_count
    new_proof = Proof(statement=new_statement, rules=new_rules, lines=new_lines+[extra_line3])
    return new_proof
    # Task 5.3b

def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    A = proof.statement.assumptions[:-1]
    fi = proof.statement.assumptions[-1]
    new_conclusion = Formula(root='->', first=fi, second=proof.statement.conclusion)
    new_statement = InferenceRule(assumptions=A, conclusion=new_conclusion)
    new_rules = proof.rules | {MP, I0, I1, D}
    new_lines = list()
    new_map = {}  # map indexes in proof to corresponding indexes in new proof
    counter = 0
    for cur_line in proof.lines:

        xsi_i = cur_line.formula
        if xsi_i in A:  # so xsi_i is a legal assumption
            idx = len(new_lines)
            first_line = Proof.Line(formula=xsi_i)  # valid as an assumption  # its index is idx
            f1 = Formula(root='->', first=fi, second=xsi_i)  # index is idx+1
            f2 = Formula(root='->', first=xsi_i, second=f1)
            second_line = Proof.Line(formula=f2, rule=I1, assumptions=[])
            f3 = Formula(root='->', first=fi, second=xsi_i)
            third_line = Proof.Line(formula=f3, rule=MP, assumptions=[idx, idx+1])
            new_lines += [first_line, second_line, third_line]
            new_map[counter] = idx+2  # index of corresponding line

        elif xsi_i == fi:  # so current formula is an assumption we can no longer use
            f1 = Formula(root='->', first=fi, second=fi)
            first_line = Proof.Line(formula=f1, rule=I0, assumptions=[])
            new_lines += [first_line]
            new_map[counter] = len(new_lines) - 1

        elif cur_line.rule == MP:  # so xsi_i was deduced by MP
            # can rely on the fact that have already deduced have ‘(φ→ξj )’ and ‘(φ→ξk)’ in the new proof!

            # we need to map old indexes to new proof indexes
            j = cur_line.assumptions[0]  # these are indexes in old proof
            k = cur_line.assumptions[1]
            new_j = new_map[j]  # index of (φ→ξj )
            new_k = new_map[k]  # index of (φ→ξk)
            # those are indexes of formulas i need in NEWPROOF!!
            # use D
            fi_imp_xsi_i = Formula(root='->', first=fi, second=xsi_i)
            fi_imp_xsi_k = new_lines[new_k].formula  # (φ→ξk) == (φ→(ξj->ξi))
            fi_imp_xsi_j = new_lines[new_j].formula

            xsi_j = proof.lines[j].formula
            xsi_j_imp_xsi_i = Formula(root='->', first=xsi_j, second=xsi_i)
            assert fi_imp_xsi_k == Formula(root='->', first=fi, second=xsi_j_imp_xsi_i)

            f2 = Formula(root='->', first=fi_imp_xsi_j, second=fi_imp_xsi_i)
            f = Formula(root='->', first=fi_imp_xsi_k, second=f2)
            idx = len(new_lines)
            line_1 = Proof.Line(formula=f, rule=D, assumptions=[])  # index will be idx
            line_2 = Proof.Line(formula=f2, rule=MP, assumptions=[new_k, idx])  # [index of fi-> xsi_k, index of line 1]
            line_3 = Proof.Line(formula=fi_imp_xsi_i, rule=MP, assumptions=[new_j, idx+1])
            new_lines += [line_1, line_2, line_3]
            new_map[counter] = idx+2

        else:
            # xsi_i is deduced by some inference rule that is not MP
            # so it has no assumptions
            # step 1: deduce xsi_i in same way in new proof
            # cur_line.rule  # this is the inference rule that has no assumptions
            idx = len(new_lines)
            first_line = cur_line  # index is idx
            f1 = Formula(root='->', first=fi, second=xsi_i)  # index is idx+1
            f2 = Formula(root='->', first=xsi_i, second=f1)
            second_line = Proof.Line(formula=f2, rule=I1, assumptions=[])
            f3 = Formula(root='->', first=fi, second=xsi_i)
            third_line = Proof.Line(formula=f3, rule=MP, assumptions=[idx, idx + 1])
            new_lines += [first_line, second_line, third_line]
            new_map[counter] = idx + 2  # index of corresponding line

        counter += 1

    new_proof = Proof(statement=new_statement, rules=new_rules, lines=new_lines)
    return new_proof





def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    combined_proof = combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)
    return combined_proof

def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    modified_proof = remove_assumption(proof)

    not_fi = proof.statement.assumptions[-1]
    fi = not_fi.first

    not_p_imp_p = proof.statement.conclusion
    p_imp_p = not_p_imp_p.first

    f1 = Formula(root='->', first=not_fi, second=not_p_imp_p)
    f2 = Formula(root='->', first=p_imp_p, second=fi)

    use_n = Formula(root='->', first=f1, second=f2)
    idx = len(modified_proof.lines)  # index of first extra line
    extra_line_0 = Proof.Line(formula=use_n, rule=N, assumptions=[])  # index is idx
    extra_line_1 = Proof.Line(formula=f2, rule=MP, assumptions=[idx-1, idx])  # idx+1
    extra_line_2 = Proof.Line(p_imp_p, rule=I0, assumptions=[])  # idx+2
    extra_line_3 = Proof.Line(formula=fi, rule=MP, assumptions=[idx+2, idx+1])  # idx+3

    new_lines = list(modified_proof.lines) + [extra_line_0, extra_line_1, extra_line_2, extra_line_3]
    new_conclusion = fi
    statement = InferenceRule(assumptions=modified_proof.statement.assumptions, conclusion=new_conclusion)
    rules = modified_proof.rules | {N}
    new_proof = Proof(statement=statement, rules=rules, lines=new_lines)
    return new_proof



