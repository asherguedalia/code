# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """        
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()


    # Task 11.1
    # create new proof, without the previous assumption
    prover = Prover(proof.assumptions - {Schema(assumption)},
                    print_as_proof_forms)

    # todo - dictionary for line numbers instead of for loops!!!
    # map formula to line number

    for line in proof.lines:

        if isinstance(line, Proof.AssumptionLine):
            if line.formula == assumption:  # so this line is no longer legal as an assumption, add different line
                prover.add_tautology(Formula('->', assumption, assumption))
            else:

                # so its an assumption we are allowed to have, add it also here
                step1 = prover.add_instantiated_assumption(line.formula, line.assumption, line.instantiation_map)
                f = Formula('->', assumption, line.formula)
                step2 = prover.add_tautology(Formula('->', line.formula, f))
                prover.add_mp(f, step1, step2)


        elif isinstance(line, proof.TautologyLine):
            step1 = prover.add_tautology(line.formula)
            f = Formula('->', assumption, line.formula)
            step2 = prover.add_tautology(Formula('->', line.formula, f))
            prover.add_mp(f, step1, step2)

        elif isinstance(line, proof.MPLine):
            # so find corresponding lines already writen to this MP's and use tautological inference
            first_num = line.conditional_line_number
            sec_num = line.antecedent_line_number
            f1 = proof.lines[first_num].formula
            f2 = proof.lines[sec_num].formula
            cur_f1 = Formula('->', assumption, f1)
            cur_f2 = Formula('->', assumption, f2)
            # now find the line numbers in prover
            cur_first_num, cur_sec_num = -1, -1
            for i in range(len(prover._lines)):
                if prover._lines[i].formula == cur_f1:
                    cur_first_num = i
                if prover._lines[i].formula == cur_f2:
                    cur_sec_num = i

            assert cur_first_num >= 0 and cur_sec_num >= 0

            prover.add_tautological_implication(Formula('->', assumption, line.formula), {cur_first_num, cur_sec_num})

        elif isinstance(line, Proof.UGLine):
            # so its a UG line, handle differently
            predicate = proof.lines[line.predicate_line_number].formula
            quantified_predicate = line.formula
            quantified_var = quantified_predicate.variable
            cur_f = Formula('->', assumption, predicate)
            cur_line_num = -1
            for i in range(len(prover._lines)):
                if prover._lines[i].formula == cur_f:
                    cur_line_num = i
                    break

            assert cur_line_num >= 0
            f1 = Formula('A', quantified_var, cur_f)
            f2 = Formula('->', assumption, quantified_predicate)
            step1 = prover.add_ug(f1, cur_line_num)

            step2 = prover.add_instantiated_assumption(Formula('->', f1, f2), prover.US, {
                'Q': assumption, 'R': predicate.substitute({str(quantified_var): Term('_')}, set()), 'x': quantified_var})
            prover.add_mp(Formula('->', assumption, line.formula), step1, step2)

        else:
            raise Exception('why are you here retard!!!!')

    return prover.qed()





def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2
