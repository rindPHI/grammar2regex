from enum import Enum
from typing import Dict, List, Tuple, Union, Generator

import z3

from nfa import NFA
from grammargraph import GrammarGraph, NonterminalNode, ChoiceNode, TerminalNode, Node

Nonterminal = str
Grammar = Dict[Nonterminal, List[str]]


class GrammarType(Enum):
    UNDET = 0  # Yet unknown, or neither left- nor rightlinear (tree structure)
    LEFT_LINEAR = 1
    RIGHT_LINEAR = 2


def state_generator(base: str) -> Generator[str, None, None]:
    i = 1
    while True:
        yield f"{base}_{i}"
        i += 1


class RegexConverter:
    def __init__(self, grammar):
        self.grammar = grammar
        self.grammar_type = GrammarType.UNDET
        self.grammar_graph = GrammarGraph.from_grammar(grammar)

    def to_dfa(self, node: Union[str, Node]) -> Union[NFA, None]:
        # TODO: Only works for epsilon-free grammars...
        #       http://www.cs.um.edu.mt/gordon.pace/Research/Software/Relic/Transformations/RG/toFSA.html
        # TODO: For left-linear grammars, have to invert the grammar and then the resulting DFA
        # TODO: Currently, we're computing an NFA. Have to turn this into DFA later.

        if type(node) is str:
            node = self.grammar_graph.get_node(node)
            assert node
        assert type(node) is NonterminalNode

        check_result = self.is_regular(node)
        if not check_result:
            return None

        nfa = NFA()
        final_state = "[final]"
        nfa.add_state(final_state, final=True)

        for nonterminal in GrammarGraph(node).to_grammar():
            makeinitial = False
            if nonterminal == node.symbol:
                makeinitial = True

            nfa.add_state(self.grammar_graph.get_node(nonterminal).quote_symbol(), initial=makeinitial)

        visited = [node]
        queue = [node]

        while queue:
            node: NonterminalNode
            node = queue.pop()
            visited.append(node)

            choice_node: ChoiceNode
            for choice_node in node.children:
                children = choice_node.children
                current_state = node.quote_symbol()

                for child in children[0:-1]:
                    next_state = nfa.next_free_state(state_generator("q"))
                    nfa.add_state(next_state)

                    if type(child) is TerminalNode:
                        nfa.add_transition(current_state, z3.Re(child.symbol), next_state)
                    else:
                        if self.grammar_graph.subgraph(child).is_tree():
                            nfa.add_transition(current_state, self.regular_expression_from_tree(child), next_state)
                        else:
                            sub_dfa = self.to_dfa(child)
                            sub_dfa.substitute_final_state(next_state)
                            nfa.transitions.update(sub_dfa.transitions)
                            nfa.add_transition(current_state, z3.Re(""), sub_dfa.initial_state)

                    current_state = next_state

                child = children[-1]

                if type(child) is TerminalNode:
                    nfa.add_transition(current_state, z3.Re(child.symbol), final_state)
                else:
                    nfa.add_transition(current_state, z3.Re(""), child.quote_symbol())
                    if child not in visited:
                        visited.append(child)
                        queue.append(child)

        return nfa

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

        if not call_seq:
            self.grammar_type = GrammarType.UNDET

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
        # are always at the left- or rightmost position, and all others are regular.

        choice_node: ChoiceNode
        for choice_node in nonterminal.children:
            found_backlink = False
            backlink_position = -1
            for index, child in enumerate(choice_node.children):
                if type(child) is TerminalNode:
                    continue

                child: NonterminalNode
                if (self.grammar_graph.subgraph(child).is_tree() or
                        (not self.grammar_graph.reachable(child, nonterminal) and
                         self.is_regular(child, call_seq + (nonterminal,)))):
                    continue

                if found_backlink:
                    return False

                found_backlink = True
                backlink_position = index

            assert not found_backlink or backlink_position >= 0

            if found_backlink and len(choice_node.children) > 1:
                if backlink_position == 0:
                    if self.grammar_type == GrammarType.RIGHT_LINEAR:
                        return False
                    self.grammar_type = GrammarType.LEFT_LINEAR
                elif backlink_position == len(choice_node.children) - 1:
                    if self.grammar_type == GrammarType.LEFT_LINEAR:
                        return False
                    self.grammar_type = GrammarType.RIGHT_LINEAR
                else:
                    return False

        all_nontree_children_nonterminals = set([])
        for choice_node in nonterminal.children:
            for child in choice_node.children:
                if type(child) is NonterminalNode and not self.grammar_graph.subgraph(child).is_tree():
                    all_nontree_children_nonterminals.add(child)

        return all([self.is_regular(child, call_seq + (nonterminal,)) for child in all_nontree_children_nonterminals])
