# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/syntax.py

"""Syntactic handling of first-order formulas and terms."""

from __future__ import annotations

from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import frozen
from propositions.syntax import Formula as PropositionalFormula, \
    is_variable as is_propositional_variable


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context."""

    def __init__(self, variable_name: str) -> None:
        """Initializes a `ForbiddenVariableError` from its offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it was to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd'))
             and s.isalnum()) or s == '_'

def is_variable(s: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()

def is_function(s: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()

@frozen
class Term:
    """An immutable first-order term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str,
                 arguments: Optional[Sequence[Term]] = None) -> None:
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1
        if not is_function(self.root):
            return self.root

        # if here so we are a function
        new_string = '('
        for arg in self.arguments:
            new_string += (str(arg) + ',')
        new_string = new_string[:-1] + ')'
        return self.root + new_string

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3.1
        if len(s) == 0:
            raise Exception('Cannot parse empty string')

        if s[0] == '_':
            return Term(root='_'), s[1:]

        # get to the end of the name
        i = 1
        for i in range(1, len(s)):
            if not s[i].isalnum():
                i -= 1
                break

        if is_constant(s[0]) or is_variable(s[0]):
            return Term(root=s[:i+1]), s[i+1:]

        if is_function(s[0]):
            # first get the name
            func_name = s[:i+1]
            # now parse all arguments separately
            args = []
            assert s[i+1] == '('
            rest = ',' + s[i+2:]
            while rest[0] == ',':  # should end when we reach ')' instead of ','
                cur_arg, rest = Term.parse_prefix(rest[1:])
                args.append(cur_arg)

            assert rest[0] == ')'
            assert len(args) > 0

            return Term(root=func_name, arguments=args), rest[1:]


        raise Exception('Illegal prefix')


    @staticmethod
    def parse(s: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            s: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3.2
        return Term.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5.1
        # add root if is constant
        constants = set()
        if is_constant(self.root):
            constants.add(self.root)
        # add all sub-terms' constants
        try:
            for term in self.arguments:
                constants.update(term.constants())
            return constants
        except AttributeError:
            return constants

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5.2
        # get root if it's a variable
        variables = set()
        if is_variable(self.root):
            variables.add(self.root)
        # get all sub-terms' variables
        try:
            for term in self.arguments:
                variables.update(term.variables())
            return variables
        except AttributeError:
            return variables

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5.3
        # add root if it is a function
        funcs = set()
        if is_function(self.root):
            name = self.root
            arity = len(self.arguments)
            funcs.add((name, arity))
        # add all sub-terms' functions
        try:
            for term in self.arguments:
                funcs.update(term.functions())
            return funcs
        except AttributeError:
            return funcs

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

        # check for illegal variable
        # after

        if is_constant(self.root) or is_variable(self.root):

            if self.root not in substitution_map:
                return self
            sub = substitution_map[self.root]
            sub_vars = sub.variables()
            for variable in forbidden_variables:
                if variable in sub_vars:
                    raise ForbiddenVariableError(str(variable))
            return sub

        if is_function(self.root):
            new_args = [t.substitute(substitution_map, forbidden_variables) for t in self.arguments]
            return Term(root=self.root, arguments=new_args)

        raise Exception('Should not be here!')



def is_equality(s: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return s == '='

def is_relation(s: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()

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
    return s == '&' or s == '|' or s == '->'

def is_quantifier(s: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return s == 'A' or s == 'E'

@frozen
class Formula:
    """An immutable first-order formula in tree representation, composed from
    relation names applied to first-order terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the the root, if
                the root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate           
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2
        if is_equality(self.root):
            return str(self.arguments[0]) + self.root + str(self.arguments[1])

        if is_relation(self.root):
            s = self.root + '('
            if len(self.arguments) == 0:
                return s + ')'

            for arg in self.arguments:
                s += (str(arg) + ',')
            return s[:-1] + ')'

        if is_unary(self.root):
            return self.root + str(self.first)

        if is_binary(self.root):
            return '(' + str(self.first) + self.root + str(self.second) + ')'

        if is_quantifier(self.root):
            return self.root + self.variable + '[' + str(self.predicate) + ']'

        raise Exception('Illegal Input!')






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
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.4.1
        if len(s) == 0:
            raise Exception('Cannot Parse Empty String!')
        if is_constant(s[0]) or is_variable(s[0]) or is_function(s[0]):
            # so we start with a term
            # assuming it has to be a term=term
            t1, r = Term.parse_prefix(s)
            assert r[0] == '='
            t2, r = Term.parse_prefix(r[1:])
            return Formula(root='=', arguments_or_first_or_variable=[t1, t2]), r

        if is_relation(s[0]):
            # get name of relation
            i = 1
            for i in range(1, len(s)):
                if not s[i].isalnum():
                    i -= 1
                    break
            relation_name = s[:i+1]
            # now parse all arguments separately
            args = []
            assert s[i + 1] == '('

            if s[i+2] == ')':
                # so there are no arguments
                return Formula(root=relation_name, arguments_or_first_or_variable=[]), s[i+3:]

            rest = ',' + s[i + 2:]
            while rest[0] == ',':  # should end when we reach ')' instead of ','
                cur_arg, rest = Term.parse_prefix(rest[1:])
                args.append(cur_arg)

            assert rest[0] == ')'
            assert len(args) > 0

            return Formula(root=relation_name, arguments_or_first_or_variable=args), rest[1:]

        if is_unary(s[0]):
            first, r = Formula.parse_prefix(s[1:])
            return Formula(root=s[0], arguments_or_first_or_variable=first), r

        if s[0] == '(':
            # so we need to expect some binary operator in the middle
            # look for a closing one
            counter = 1
            for i in range(1, len(s)):
                if s[i] == ')':
                    counter -= 1
                    if counter < 0:
                            raise Exception('too many closing brackets')
                    if counter == 0:
                        # so this is the one that closes what we opened
                        remainder = s[i + 1:]

                        p1, r1 = Formula.parse_prefix(s[1:i])  # take whats inside but expect a binary op
                        # we want to parse all what was in the brackets so continue parsing until r is ''
                        if len(r1) > 0 and is_binary(r1[0]):  # so binary op of len 1
                            j = 1
                        elif len(r1) > 1 and is_binary(r1[0:2]):  # so binary op of len 2
                            j = 2
                        elif len(r1) > 2 and is_binary(r1[0:3]):  # so binary op of len 3
                            j = 3
                        else:
                            raise Exception('we need to see a binary op if we saw brackets')

                        # so it is the root and we parse the second half
                        p2, r2 = Formula.parse_prefix(r1[j:])
                        # now if len(r) > 0 its illegal cuz we had a binary operator
                        if len(r2) > 0 or p2 is None:
                            raise Exception('Illegal, we saw a binary op or illegal inside formula')

                        new_formula = Formula(root=r1[0:j], arguments_or_first_or_variable=p1, second_or_predicate=p2)
                        return new_formula, remainder

                if s[i] == '(':
                    counter += 1
            raise Exception('Illegal Brackets boyy')

        if is_quantifier(s[0]):
            quant = s[0]
            assert '[' in s[1:]
            split_str = s[1:].split('[')
            t1, rem = Term.parse_prefix(split_str[0])
            assert len(rem) == 0
            var = str(t1)
            assert is_variable(var)


            # now we have a something like ....] we need to fins the matching bracket
            cur_s = s[1+len(var)+1:]  # this is the string ...]
            counter = 1
            for i in range(len(cur_s)):
                if cur_s[i] == ']':
                    counter -= 1
                    if counter == 0:
                        # so we found our matching bracket
                        fi, extra = Formula.parse_prefix(cur_s[:i])
                        assert len(extra) == 0
                        return Formula(root=quant, arguments_or_first_or_variable=var, second_or_predicate=fi), cur_s[i+1:]
                if cur_s[i] == '[':
                    counter += 1

            raise Exception('bad input in square brackets')


        raise Exception('Who Are You???')

    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4.2
        return Formula.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6.1
        constants = set()
        # if relation or equality --> return all arguments' constants
        if is_relation(self.root) or is_equality(self.root):
            for a in self.arguments:
                constants.update(a.constants())
            return constants
        # if quantifier --> return predicate's constants
        if is_quantifier(self.root):
            return self.predicate.constants()
        # if unary --> return first's constants
        if is_unary(self.root):
            return self.first.constants()
        # if binary --> return union of first's and second's constants
        if is_binary(self.root):
            return self.first.constants().union(self.second.constants())

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6.2
        variables = set()
        # if relation or equality --> return all arguments' variables
        if is_relation(self.root) or is_equality(self.root):
            for a in self.arguments:
                variables.update(a.variables())
            return variables
        # if quantifier --> return variable union predicate's-variables
        if is_quantifier(self.root):
            variables.add(self.variable)
            variables.update(self.predicate.variables())
            return variables
        # if unary --> return first's variables
        if is_unary(self.root):
            return self.first.variables()
        # if binary --> return union of first's and second's variables
        if is_binary(self.root):
            return self.first.variables().union(self.second.variables())

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of all variable names used in the current formula not only
            within a scope of a quantification on those variable names.
        """
        # Task 7.6.3
        variables = set()
        # if relation or equality --> return all arguments' variables
        if is_relation(self.root) or is_equality(self.root):
            for a in self.arguments:
                variables.update(a.variables())
            return variables
        # if quantifier --> return predicate's free-variables w/o variable
        if is_quantifier(self.root):
            return self.predicate.free_variables() - set(self.variable)
        # if unary --> return first's free variables
        if is_unary(self.root):
            return self.first.free_variables()
        # if binary --> return union of first's and second's free variables
        if is_binary(self.root):
            return self.first.free_variables().union(self.second.free_variables())

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6.4
        funcs = set()
        # if relation --> return this function and all arguments' functions
        if is_relation(self.root):
            if is_function(self.root):
                funcs.add((self.root, len(self.arguments)))
            for a in self.arguments:
                funcs.update((a.functions()))
            return funcs
        # if equality --> return all arguments' functions
        if is_equality(self.root):
            for a in self.arguments:
                funcs.update((a.functions()))
            return funcs
        # if quantifier --> return predicate's functions
        if is_quantifier(self.root):
            return self.predicate.functions()
        # if unary --> return first's functions
        if is_unary(self.root):
            return self.first.functions()
        # if binary --> return union of first's and second's functions
        if is_binary(self.root):
            return self.first.functions().union(self.second.functions())


    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6.5
        relations = set()
        # if relation --> return this relation
        if is_relation(self.root):
            relations.add((self.root, len(self.arguments)))
            return relations
        # if equality --> return empty set
        if is_equality(self.root):
            return set()
        # if quantifier --> return predicate's relations
        if is_quantifier(self.root):
            return self.predicate.relations()
        # if unary --> return first's relations
        if is_unary(self.root):
            return self.first.relations()
        # if binary --> return union of first's and second's relations
        if is_binary(self.root):
            return self.first.relations().union(self.second.relations())

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
                Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

        if is_equality(self.root):
            t1 = self.arguments[0].substitute(substitution_map, forbidden_variables)
            t2 = self.arguments[1].substitute(substitution_map, forbidden_variables)
            return Formula(root='=', arguments_or_first_or_variable=[t1, t2])

        if is_relation(self.root):
            new_args = [t.substitute(substitution_map, forbidden_variables) for t in self.arguments]
            return Formula(root=self.root, arguments_or_first_or_variable=new_args)

        if is_unary(self.root):
            return Formula(self.root, self.first.substitute(substitution_map, forbidden_variables))

        if is_binary(self.root):
            return Formula(self.root, self.first.substitute(substitution_map, forbidden_variables),
                           self.second.substitute(substitution_map, forbidden_variables))

        if is_quantifier(self.root):
            # so substitute inner formula but make the quantified variable also forbidden

            #  remove entry of bounded variables so they do not get subbed
            if self.variable in substitution_map.keys():
                substitution_map = dict(substitution_map)
                del substitution_map[self.variable]

            predicate = self.predicate.substitute(substitution_map, forbidden_variables | {self.variable})
            return Formula(self.root, self.variable, predicate)

        raise Exception('why are you here??')



    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a map from each atomic
            propositional formula to the subformula for which it was
            substituted.
        """
        # Task 9.6

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a first-order formula from a propositional skeleton and a
        substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute.
            substitution_map: a map from each atomic propositional subformula
                of the given skeleton to a first-order formula.

        Returns:
            A first-order formula obtained from the given propositional skeleton
            by substituting each atomic propositional subformula with the formula
            mapped to it by the given map.
        """
        for key in substitution_map:
            assert is_propositional_variable(key)
        # Task 9.10
