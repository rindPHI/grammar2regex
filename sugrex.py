import copy
import itertools
import re
from enum import Enum
from typing import Dict, List, Tuple, Set, Union, Callable

import pydot
from fuzzingbook.Grammars import unreachable_nonterminals, nonterminals, is_nonterminal

from grammargraph import GrammarGraph, NonterminalNode, ChoiceNode, TerminalNode

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
        self.grammar_graph = GrammarGraph.from_grammar(grammar)

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

        # If the graph is a tree, we can easily create a regular expression with
        # concatenations and alternatives.

        if self.grammar_graph.subgraph(nonterminal).is_tree():
            return True

        # If there is recursion, check if those children nonterminals with backlinks
        # are always at the left- or rightmost position, and all others form trees.
        # Note that backlink nonterminals in middle positions are unproblematic, since
        # we can transfer them to be at either position. It only must not be mixed, and
        # there may be at most one nonterminal with backlinks.

        choice_node: ChoiceNode
        for choice_node in nonterminal.children:
            found_backlink = False
            backlink_position = -1
            for index, child in enumerate(choice_node.children):
                if type(child) is TerminalNode:
                    continue

                child: NonterminalNode
                if self.grammar_graph.subgraph(child).is_tree():
                    continue

                if found_backlink:
                    return False

                found_backlink = True
                backlink_position = index

            assert not found_backlink or backlink_position >= 0

            if len(choice_node.children) > 1:
                if backlink_position == 0:
                    if self.grammar_type == GrammarType.RIGHT_LINEAR:
                        return False
                    self.grammar_type = GrammarType.LEFT_LINEAR

                if backlink_position == len(choice_node.children) - 1:
                    if self.grammar_type == GrammarType.LEFT_LINEAR:
                        return False
                    self.grammar_type = GrammarType.RIGHT_LINEAR

        all_nontree_children_nonterminals = set([])
        for choice_node in nonterminal.children:
            for child in choice_node.children:
                if type(child) is NonterminalNode and not self.grammar_graph.subgraph(child).is_tree():
                    all_nontree_children_nonterminals.add(child)

        return all([self.is_regular(child, call_seq + (nonterminal,)) for child in all_nontree_children_nonterminals])

    @staticmethod
    def delete_unreachable(grammar: Grammar):
        for unreachable in unreachable_nonterminals(grammar):
            del grammar[unreachable]
