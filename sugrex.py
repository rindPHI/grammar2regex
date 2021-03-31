import copy
from functools import reduce

import itertools
import re
from enum import Enum
from typing import Dict, List, Tuple, Set, Union, Callable

import pydot
import z3
from fuzzingbook.Grammars import unreachable_nonterminals, nonterminals, is_nonterminal

from grammargraph import GrammarGraph, NonterminalNode, ChoiceNode, TerminalNode, Node

Nonterminal = str
Grammar = Dict[Nonterminal, List[str]]


class GrammarType(Enum):
    UNDET = 0  # Yet unknown
    LEFT_LINEAR = 1
    RIGHT_LINEAR = 2


class RegularityChecker:
    def __init__(self, grammar):
        self.grammar = grammar
        self.grammar_type = GrammarType.UNDET
        self.grammar_graph = GrammarGraph.from_grammar(grammar)

    def regular_expression_from_tree(self, node: Union[str, Node]) -> z3.ReRef:
        if type(node) is str:
            node = self.grammar_graph.get_node(node)
            assert node

        if type(node) is TerminalNode:
            return z3.Re(node.symbol)

        assert type(node) is NonterminalNode
        assert self.grammar_graph.subgraph(node).is_tree()

        node: NonterminalNode
        choice_node: ChoiceNode

        result: Union[z3.ReRef, None] = None
        for choice_node in node.children:
            children_regexes = [self.regular_expression_from_tree(child) for child in choice_node.children]
            if len(children_regexes) == 1:
                child_result = children_regexes[0]
            else:
                child_result = z3.Concat(*children_regexes)

            if result is None:
                result = child_result
            else:
                result = z3.Union(result, child_result)

        assert result is not None
        return result



    def is_regular(self, nonterminal: Union[str, NonterminalNode], call_seq: Tuple = ()) -> bool:
        """
        Checks whether the language generated from "grammar" starting in "nonterminal" is regular.
        This is the case if all productions either are left- or rightlinear, with the exception that
        they may contain nonterminals that form a tree in the grammar. Those trivially represent
        retular expressions.

        :param grammar: A context-free grammar.
        :param nonterminal: A nonterminal within this grammar.
        :param call_seq: A tuple of already seen nodes, used to break infinite recursion.
        :return: True iff the language defined by the sublanguage of grammar's language when
        starting in nonterminal is regular.
        """

        if type(nonterminal) is str:
            nonterminal = self.grammar_graph.get_node(nonterminal)
            assert nonterminal
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
