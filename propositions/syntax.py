# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulae."""

from __future__ import annotations

import copy
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen


def is_variable(s: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())


def is_constant(s: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return s == 'T' or s == 'F'


def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'


def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # For Chapter 3:
    return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}


@frozen
class Formula:
    """An immutable propositional formula in tree representation.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            does not equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1

        # base cases:
        # if only root:
        if is_variable(self.root) or is_constant(self.root):
            # so root is a constant or variable
            return self.root

        elif is_unary(self.root):
            # so root is a unary operator
            return self.root + str(self.first)

        else:
            # so root is a binary operator, recursively return
            return '(' + str(self.first) + self.root + str(self.second) + ')'

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # Task 1.2
        if is_constant(self.root):
            return set()
        if is_variable(self.root):
            # so root is a variable
            return {self.root}

        elif is_unary(self.root):
            # so root is a unary operator
            return self.first.variables()

        else:
            # so root is a binary operator, recursively return
            return self.first.variables() | self.second.variables()

    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        if is_constant(self.root):
            return {self.root}
        if is_variable(self.root):
            # so root is a variable
            return set()

        elif is_unary(self.root):
            # so root is a unary operator
            return {self.root} | self.first.operators()

        else:
            # so root is a binary operator, recursively return
            return self.first.operators() | self.second.operators() | {self.root}
        
    @staticmethod
    def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the first token of the string is a variable name (e.g.,
            ``'x12'``), then the parsed prefix will be that entire variable name
            (and not just a part of it, such as ``'x1'``). If no prefix of the
            given string is a valid standard string representation of a formula
            then returned pair should be of ``None`` and an error message, where
            the error message is a string with some human-readable content.
        """
        # Task 1.4
        # base cases
        # if first letter is constant return it.
        if len(s) == 0:
            return None, 'Error: Empty String!'  # todo- this is good for debug but its not forsure an empty string
        if is_constant(s[0]):
            return Formula(root=s[0]), s[1:]
        # if first letter is part of a variable, return it
        if is_variable(s[0]):
            i = 1
            while i < len(s):
                if not s[i].isdigit():
                    break
                i += 1
            return Formula(root=s[:i]), s[i:]

        if is_unary(s[0]):
            # so whatever is after should be eligible also without
            parsed = Formula.parse_prefix(s[1:])
            if parsed[0] is None:
                # cuz its illegal
                return parsed

            formula = parsed[0]
            new_formula = Formula(root=s[0], first=formula)
            return new_formula, parsed[1]

        # otherwise it can be '('

        if s[0] == '(':
            # look for a closing one
            counter = 1
            for i in range(1, len(s)):
                if s[i] == ')':
                    counter -= 1
                    if counter < 0:
                        return None, 'too many closing brackets'
                    if counter == 0:
                        # so this is the one that closes what we opened
                        remainder = s[i+1:]

                        p1, r1 = Formula.parse_prefix(s[1:i])  # take whats inside but expect a binary op
                        if p1 is None:  # so inside is illegal
                            return None, r1

                        # we want to parse all what was in the brackets so continue parsing until r is ''
                        if len(r1) > 0 and is_binary(r1[0]):  # so binary op of len 1
                            j = 1
                        elif len(r1) > 1 and is_binary(r1[0:2]):  # so binary op of len 2
                            j = 2
                        elif len(r1) > 2 and is_binary(r1[0:3]):  # so binary op of len 3
                            j = 3
                        else:
                            return None, 'Illegal, no binary'  # we need to see a binary op if we saw brackets

                        # so it is the root and we parse the second half
                        p2, r2 = Formula.parse_prefix(r1[j:])
                        # now if len(r) > 0 its illegal cuz we had a binary operator
                        if len(r2) > 0 or p2 is None:
                            return None, 'Illegal, we saw a binary op or illegal inside formula'

                        new_formula = Formula(root=r1[0:j], first=p1, second=p2)
                        return new_formula, remainder

                if s[i] == '(':
                    counter += 1
            return None, 'Illegal brackets'

        else:
            return None, 'Illegal Formula'

    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            s: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        f1, r1 = Formula.parse_prefix(s)
        if f1 is None:
            return False
        if not len(r1):  # because f1 is not non and we are done
            return True

        # otherwise there must be a binary operator
        # base case here - so check if we have brackets because in parse prefix we find them at the beginning
        if s[0] != '(' or s[-1] != ')':
            return False

        if len(r1) > 0 and is_binary(r1[0]):  # so binary op of len 1
            j = 1
        elif len(r1) > 1 and is_binary(r1[0:2]):  # so binary op of len 2
            j = 2
        elif len(r1) > 2 and is_binary(r1[0:3]):  # so binary op of len 3
            j = 3
        else:
            return False
        # so it is the root and we parse the second half
        f2, r2 = Formula.parse_prefix(r1[j:])
        if f2 is None or len(r2) > 0:
            return False

        return True
        
    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(s)  # we assume here it is legal
        f1, r1 = Formula.parse_prefix(s)

        # otherwise there must be a binary operator
        if len(r1) > 0 and is_binary(r1[0]):  # so binary op of len 1
            j = 1
        elif len(r1) > 1 and is_binary(r1[0:2]):  # so binary op of len 2
            j = 2
        elif len(r1) > 2 and is_binary(r1[0:3]):  # so binary op of len 3
            j = 3
        else:
            return f1
        # so it is the root and we parse the second half
        f2, r2 = Formula.parse_prefix(r1[j:])

        return Formula(root=r1[0:j], first=f1, second=f2)

        # Task 1.6

# Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(s: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

# Tasks for Chapter 3

    def substitute_variables(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((p->p)|z)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)')})
            (((q&r)->(q&r))|z)
        """

        # Task 3.3
        for variable in substitution_map:
            assert is_variable(variable)

        # go through self tree if we see the key from the map so its a leaf, repalce it with the tree of value formula
        if self.root in substitution_map.keys():
            # so root is just a variable, sub it for the value and we are done
            return copy.deepcopy(substitution_map[self.root])

        # otherwise lets check the kids
        if is_constant(self.root) or is_variable(self.root):
            return copy.deepcopy(self)  # cuz its a leaf with nothing to change

        if is_unary(self.root):
            return Formula(root=self.root, first=self.first.substitute_variables(substitution_map))

        if is_binary(self.root):
            return Formula(root=self.root, first=self.first.substitute_variables(substitution_map),
                           second=self.second.substitute_variables(substitution_map))

        else:
            raise Exception('Bad input')



    def substitute_operators(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4

        if is_binary(self.root):
            # first handle kids
            first = self.first.substitute_operators(substitution_map)
            second = self.second.substitute_operators(substitution_map)
            if self.root in substitution_map:
                # sub p for left formula sub q for right formula
                return substitution_map[self.root].substitute_variables({'p': first, 'q': second})
            return Formula(root=self.root, first=first, second=second)

        elif is_unary(self.root):
            first = self.first.substitute_operators(substitution_map)
            # sub p for left formula sub q for right formula
            if self.root in substitution_map:
                return substitution_map[self.root].substitute_variables({'p': first})
            return Formula(root=self.root, first=first)

        elif is_constant(self.root) or is_variable(self.root):
            if self.root in substitution_map:
                return substitution_map[self.root]
            return Formula(root=self.root)

        else:
            raise Exception('Bad input')

