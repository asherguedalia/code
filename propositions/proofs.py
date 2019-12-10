# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/proofs.py

"""Proofs by deduction in propositional logic."""

from __future__ import annotations

from functools import reduce
from typing import AbstractSet, Iterable, FrozenSet

from propositions.syntax import *

SpecializationMap = Mapping[str, Formula]

@frozen
class InferenceRule:
    """An immutable inference rule in propositional logic, comprised by zero
    or more assumed propositional formulae, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Iterable[Formula], conclusion: Formula) -> \
        None:
        """Initialized an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return (isinstance(other, InferenceRule) and
                self.assumptions == other.assumptions and
                self.conclusion == other.conclusion)

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))
        
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current inference
        rule.

        Returns:
            A set of all atomic propositions used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # Task 4.1
        return reduce(lambda x, y: x | y, [f.variables() for f in self.assumptions] + [self.conclusion.variables()])

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """        
        for variable in specialization_map:
            assert is_variable(variable)
        # Task 4.4
        new_assumptions = (a.substitute_variables(specialization_map) for a in self.assumptions)
        new_conclusion = self.conclusion.substitute_variables(specialization_map)
        return InferenceRule(new_assumptions, new_conclusion)



    @staticmethod
    def merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps.

        Parameters:
            specialization_map1: first map to merge, or ``None``.
            specialization_map2: second map to merge, or ``None``.

        Returns:
            A single map containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        # Task 4.5a
        if specialization_map1 is None or specialization_map2 is None:
            return None
        merged_map = {}
        for key in specialization_map1:
            merged_map[key] = specialization_map1[key]
        for key in specialization_map2:
            if key in merged_map and merged_map[key] != specialization_map2[key]:
                return None
            merged_map[key] = specialization_map2[key]  # either add new entry or they are the same

        return merged_map



        
    @staticmethod
    def formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        # Task 4.5b
        # work recursively and build the specializtion maps from bottom up, then come back up and
        # merge all the maps
        if is_constant(general.root):
            if general.root == specialization.root:
                # so its  liek asking if T is specialliztion of T which is true and give back empty map
                return {}
            return None

        if is_variable(general.root):
            # so any substitution can hold
            return {general.root: specialization}

        if is_unary(general.root):
            if general.root == specialization.root:
                return InferenceRule.formula_specialization_map(general.first, specialization.first)
            return None

        if is_binary(general.root):
            if general.root == specialization.root:
                return InferenceRule.merge_specialization_maps(
                    InferenceRule.formula_specialization_map(general.first, specialization.first),
                    InferenceRule.formula_specialization_map(general.second, specialization.second))
            return None

        raise Exception('Bad Input!')



    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # Task 4.5c
        if len(self.assumptions) != len(specialization.assumptions):
            # so im assuming it cant be ok because it isnt even the same set of rules
            return None
        merged = {}
        for f1, f2 in zip(self.assumptions, specialization.assumptions):
            merged = InferenceRule.merge_specialization_maps(InferenceRule.formula_specialization_map(f1, f2), merged)
        merged = InferenceRule.merge_specialization_maps(
            InferenceRule.formula_specialization_map(self.conclusion, specialization.conclusion), merged)
        return merged


    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None

@frozen
class Proof:
    """A frozen deductive proof, comprised of a statement in the form of an
    inference rule, a set of inference rules that may be used in the proof, and
    a proof in the form of a list of lines that prove the statement via these
    inference rules.

    Attributes:
        statement (`InferenceRule`): the statement of the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statment: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]
    
    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Iterable[Proof.Line]) -> None:
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement for the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula which
        is either justified as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule out
                of those allowed in the proof, a specialization of which
                concludes the formula, or ``None`` if the formula is justified
                as an assumption of the proof.
            assumptions
                (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): a tuple of zero
                or more indices of previous lines in the proof whose formulae
                are the respective assumptions of the specialization of the rule
                that concludes the formula, if the formula is not justified as
                an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Iterable[int]] = None) -> None:
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and indices of justifying previous lines.

            Parameters:
                formula: the formula to be justified by this line.
                rule: the inference rule out of those allowed in the proof, a
                    specialization of which concludes the formula, or ``None``
                    if the formula is to be justified as an assumption of the
                    proof.
                assumptions: an iterable over indices of previous lines in the
                    proof whose formulae are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current proof line.

            Returns:
                A string representation of the current proof line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                return str(self.formula) + ' Inference Rule ' + \
                       str(self.rule) + \
                       ((" on " + str(self.assumptions))
                        if len(self.assumptions) > 0 else '')

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None
        
    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof for ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += "Lines:\n"
        for i in range(len(self.lines)):
            r += ("%3d) " % i) + str(self.lines[i]) + '\n'
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulae justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: index of the line according to which to construct the
                inference rule.

        Returns:
            The constructed inference rule, with assumptions ordered in the
            order of their indices in the specified line, or ``None`` if the
            specified line is justified as an assumption.
            ####todo: so it seems like the assumptions tuple can be in whatever order
        """
        #line params:
        """Parameters:
                formula: the formula to be justified by this line.
                rule: the inference rule out of those allowed in the proof, a
                    specialization of which concludes the formula, or ``None``
                    if the formula is to be justified as an assumption of the
                    proof.
                assumptions: an iterable over indices of previous lines in the
                    proof whose formulae are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof."""
        assert line_number < len(self.lines)
        # Task 4.6a

        specified_line = self.lines[line_number]
        if specified_line.rule is None:
            return None  # because that means the formula is to be justified as an assumption of the proof.
        ret_conclusion = specified_line.formula  # this is what the line is saying (trying to prove)
        assert specified_line.assumptions is not None  # 'should not be None because rule is not None'
        ret_assumptions = []
        for cur_line_idx in specified_line.assumptions:
            ret_assumptions.append(self.lines[cur_line_idx].formula)

        return InferenceRule(ret_assumptions, ret_conclusion)


    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.


        Parameters:
            line_number: index of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            then ``True`` if and only if all of the following hold:

            1. The rule specified for that line is one of the allowed inference
               rules in the current proof.
            2. Some specialization of the rule specified for that line has
               the formula justified by that line as its conclusion,(and its assumptions are:) and the
               formulae justified by the lines specified as the assumptions of
               that line (in the order of their indices in this line) as its
               assumptions.
        """
        assert line_number < len(self.lines)
        specified_line = self.lines[line_number]
        if specified_line.rule is None:
            # so specified line is justified as an assumption
            return specified_line.formula in self.statement.assumptions
            # so the formula justified by this line is an assumption of the current proof
            # so line is legal, otherwise its an assumption that we didnt assume for this proof! so its not legal

        is_based_on_prev_lines = max(specified_line.assumptions, default=-1) < line_number
        second_condition = self.rule_for_line(line_number).is_specialization_of(specified_line.rule) and is_based_on_prev_lines
        if specified_line.rule in self.rules and second_condition:
            return True
        return False





        # Task 4.6b
        
    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.
        #

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c
        # check that all lines are valid
        assert len(self.lines) > 0 # cuz im assuming the last line is the proof so there has to be at least one line
        lines_valid = reduce(lambda x, y: x and y, [self.is_line_valid(i) for i in range(len(self.lines))], True)
        return lines_valid and self.statement.conclusion == self.lines[-1].formula

        # check that statement holds with these assumptions, so make statement just a line so that its formula is conclusion
        # wait is conclusion supposed just to be the last line??
        # i guess check if statement.assumption all are in one of the lines. and if so conclusion is true.

# Chapter 5 tasks

def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule into a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the conclusion of the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    # get specializtion map
    spec_map = proof.statement.specialization_map(specialization)
    spec_assumptions = [a.substitute_variables(spec_map) for a in proof.statement.assumptions]
    spec_conclusion = proof.statement.conclusion.substitute_variables(spec_map)

    spec_statement = InferenceRule(assumptions=spec_assumptions, conclusion=spec_conclusion)
    # rules should be the same because they were not speciallized anyway
    spec_lines = list()

    for l in proof.lines:

        if not l.is_assumption():
            new_line = Proof.Line(formula=l.formula.substitute_variables(spec_map),
                                  rule=copy.deepcopy(l.rule), assumptions=copy.copy(l.assumptions))
        else:
            new_line = Proof.Line(formula=l.formula.substitute_variables(spec_map))
        spec_lines.append(new_line)

    # not deepcopying rules here because they are frozen set so cant be changed
    return Proof(statement=spec_statement, rules=proof.rules, lines=spec_lines)

    # Task 5.1

def inline_proof_once(main_proof: Proof, line_number: int, lemma_proof: Proof) \
    -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line: index of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating line indices specified throughout the proof to maintain the
        validity of the proof. The set of allowed inference rules in the
        returned proof is the union of the rules allowed in the two given
        proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()
    cur_line = main_proof.lines[line_number]

    # get list of formulas we assumed that we want to specialize to
    spec_assumptions_for_lemma = [main_proof.lines[i].formula for i in cur_line.assumptions]
    # create new inference rule which is how we want the lemmas proof to look after we specailze it so it
    # fits as is in the line of main_proof
    new_spec_inference_rule = InferenceRule(assumptions=spec_assumptions_for_lemma,
                             conclusion=cur_line.formula)
    spec_proof = prove_specialization(proof=lemma_proof, specialization=new_spec_inference_rule)
    # now i need to replace my line with all these lines, and update all indexes
    # get length of lines
    index_addition = len(spec_proof.lines) - 1  # because final line stayed so it don't count for addition
    # create new proof with these lines, and all rules
    new_rules = main_proof.rules | lemma_proof.rules  # no copy frozen set
    sp_lines_no_assumptions = list()
    need_a_break = False
    for i in range(len(spec_proof.lines)):
        l = spec_proof.lines[i]
        if l.is_assumption():
            if l.formula not in main_proof.statement.assumptions:
                need_a_break = True
                # so we need to copy the main proof line that corresponds to this assumption and replace
                for idx in main_proof.lines[line_number].assumptions:  # must have assumptions cuz our lemma is
                    # assuming something which is why we are here in the first place
                    main_proof_line = main_proof.lines[idx]
                    if main_proof_line.formula == l.formula:
                        new_line = Proof.Line(formula=l.formula, rule=main_proof_line.rule,
                                              assumptions=main_proof_line.assumptions)
                        need_a_break = False
                        break
            else: # so it is justified as an assumption
                new_line = Proof.Line(formula=l.formula)
        else:
            # update the indexes
            new_line = Proof.Line(formula=l.formula, rule=l.rule, assumptions=[j + line_number for j in l.assumptions])

        assert not need_a_break
        sp_lines_no_assumptions.append(new_line)  # new line should always be defined.

    new_lines = list(main_proof.lines)[:line_number] + sp_lines_no_assumptions + list(
        main_proof.lines[line_number+1:])
    # update indexes

    # now go through rest of lines that are old but if they used cur line update its index
    # also update indexes for all lines after cur line
    for i in range(line_number+index_addition + 1, len(new_lines)):
        if not new_lines[i].is_assumption():
            new_assumptions_idx = []
            for a in new_lines[i].assumptions:
                if a >= line_number:
                    new_assumptions_idx.append(a+index_addition)
                else:
                    new_assumptions_idx.append(a)
            new_lines[i] = Proof.Line(formula=new_lines[i].formula, rule=new_lines[i].rule,
                                      assumptions=new_assumptions_idx)

    return Proof(statement=main_proof.statement, lines=new_lines, rules=new_rules)


    # Task 5.2a

def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the rules
        allowed in the two given proofs but without the "lemma" rule proved by
        `lemma_proof`.
    """
    # Task 5.2b
    new_proof = main_proof
    i = 0
    while i < len(new_proof.lines):
        if not new_proof.lines[i].is_assumption():
            if lemma_proof.statement == new_proof.lines[i].rule:
                new_proof = inline_proof_once(new_proof, i, lemma_proof)
        i += 1

    return Proof(statement=new_proof.statement, rules=new_proof.rules - {lemma_proof.statement}, lines=new_proof.lines)