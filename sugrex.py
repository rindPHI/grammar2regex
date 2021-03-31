import copy
import itertools
import re
from enum import Enum
from typing import Dict, List, Tuple, Set, Union, Callable

import pydot
from fuzzingbook.Grammars import unreachable_nonterminals, nonterminals, is_nonterminal

from grammargraph import GrammarGraph, NonterminalNode

Nonterminal = str
Grammar = Dict[Nonterminal, List[str]]


class GrammarType(Enum):
    UNDET = 0  # Yet unknown
    NON_RECURSIVE = 1  # Expansions form a non-recursive "call tree" without backlinks
    LEFT_LINEAR = 2
    RIGHT_LINEAR = 3


class RegularityChecker:
    def __init__(self, grammar):
        self.grammar = grammar
        self.grammar_type = GrammarType.UNDET
        self.grammar_graph = GrammarGraph(grammar)

    def is_regular(self, nonterminal: Union[str, NonterminalNode], call_seq: Tuple = ()) -> bool:
        """
        Checks whether the language generated from "grammar" starting in "nonterminal" is regular.
        This is the case if

        1. all productions either are left- or rightlinear, or
        2. refer to nonterminals constructing a regular language. There must be no back-references from those.

        :param grammar: A context-free grammar.
        :param nonterminal: A nonterminal within this grammar.
        :return: True iff the language defined by the sublanguage of grammar's language when
        starting in nonterminal is regular.
        """

        if type(nonterminal) is str:
            nonterminal = self.grammar_graph.get_node(nonterminal)
        nonterminal: NonterminalNode

        if nonterminal in call_seq:
            return True

        nonterminal_symbols: Set[str] = \
            set(itertools.chain(*[nonterminals(expansion) for expansion in self.grammar[nonterminal]]))

        if not nonterminal_symbols:
            return True

        if nonterminal not in nonterminal_symbols:
            if any([self.grammar_graph.reachable(self.grammar_graph.get_node(child_nonterminal),
                                                 self.grammar_graph.get_node(nonterminal))
                    for child_nonterminal in nonterminal_symbols]):
                return False
            return all([self.is_regular(child_nonterminal, call_seq + (nonterminal,))
                        for child_nonterminal in nonterminal_symbols])

        for expansion in self.grammar[nonterminal]:
            nonterminals_in_expansion = set(nonterminals(expansion))

            if not nonterminals_in_expansion:
                continue

            if len(nonterminals_in_expansion) > 1:
                return False

            nonterminal_in_expansion = list(nonterminals_in_expansion)[0]

            expansion_elements = re.sub(f"({re.escape(nonterminal_in_expansion)})",
                                        '[cut]\\1[cut]',
                                        expansion).split("[cut]")
            index = expansion_elements.index(nonterminal_in_expansion)

            if index == len(expansion_elements) - 1:
                if self.grammar_type == GrammarType.LEFT_LINEAR:
                    return False
                if self.grammar_type == GrammarType.UNDET:
                    self.grammar_type = GrammarType.RIGHT_LINEAR

            if index == 0:
                if self.grammar_type == GrammarType.RIGHT_LINEAR:
                    return False
                if self.grammar_type == GrammarType.UNDET:
                    self.grammar_type = GrammarType.LEFT_LINEAR

            # Middle positions can be converted to either option

            if not self.is_regular(nonterminal_in_expansion, call_seq + (nonterminal,)):
                return False

        return True

    @staticmethod
    def delete_unreachable(grammar: Grammar):
        for unreachable in unreachable_nonterminals(grammar):
            del grammar[unreachable]
