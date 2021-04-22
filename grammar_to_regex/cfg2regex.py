import copy
import logging
from enum import Enum
from typing import Dict, List, Tuple, Union, Generator, Set

import itertools
import z3
from orderedset import OrderedSet

from grammar_to_regex.grammargraph import GrammarGraph, NonterminalNode, ChoiceNode, TerminalNode, Node
from grammar_to_regex.helpers import reverse_grammar, split_expansion, expand_nonterminals, delete_unreachable
from grammar_to_regex.nfa import NFA, Transition
from grammar_to_regex.type_defs import Grammar, Nonterminal


class GrammarType(Enum):
    UNDET = 0  # Yet unknown, or neither left- nor rightlinear (tree structure)
    LEFT_LINEAR = 1
    RIGHT_LINEAR = 2


def state_generator(base: str) -> Generator[str, None, None]:
    i = 1
    while True:
        yield f"{base}_{i}"
        i += 1


def re_concat(*regular_expressions: z3.ReRef) -> z3.ReRef:
    regular_expressions = [regex for regex in regular_expressions if not regex.eq(z3.Re(""))]

    if not regular_expressions:
        return z3.Re("")
    elif len(regular_expressions) == 1:
        return regular_expressions[0]
    else:
        return z3.Concat(*regular_expressions)


class RegexConverter:
    def __init__(self, grammar: Grammar, max_num_expansions: int = 10):
        """
        :param grammar: The underlying grammar.
        :param max_num_expansions: For non-regular (sub) grammars, we can unwind problematic nonterminals in
                                   expansions. This parameter sets a depth bound on the number of unwindings.
        """

        self.grammar: Grammar = grammar
        self.max_num_expansions = max_num_expansions

        self.grammar_type: GrammarType = GrammarType.UNDET
        self.grammar_graph: GrammarGraph = GrammarGraph.from_grammar(grammar)

        self.logger = logging.Logger("RegexConverter")

    def left_linear_grammar_to_regex(self, node_symbol: Union[str, Node]) -> z3.ReRef:
        node = self.str_to_nonterminal_node(node_symbol)
        self.assert_regular(node)
        assert self.grammar_type == GrammarType.LEFT_LINEAR

        old_grammar_graph = self.grammar_graph
        self.grammar_graph = GrammarGraph.from_grammar(reverse_grammar(self.grammar))
        # Grammar represented by graph is right-linear now

        nfa = self.right_linear_grammar_to_nfa(node_symbol)
        assert nfa is not None
        nfa = nfa.reverse()

        self.grammar_graph = old_grammar_graph
        return self.nfa_to_regex(nfa)

    def right_linear_grammar_to_regex(self, node: Union[str, Node]) -> z3.ReRef:
        node = self.str_to_nonterminal_node(node)
        self.assert_regular(node)
        assert self.grammar_type != GrammarType.LEFT_LINEAR

        nfa = self.right_linear_grammar_to_nfa(node)
        assert nfa is not None

        return RegexConverter.nfa_to_regex(nfa)

    @staticmethod
    def nfa_to_regex(nfa: Union[NFA, None]) -> z3.ReRef:
        def label_from_singleton_tr(transitions: List[Transition]) -> Union[None, z3.ReRef]:
            return None if not transitions else transitions[0][1]

        while len(nfa.states) > 2:
            s = [state for state in nfa.states if state not in (nfa.initial_state, nfa.final_state)][0]

            predecessors = [p for p in nfa.predecessors(s) if p != s]
            successors = [q for q in nfa.successors(s) if q != s]
            loops = nfa.transitions_between(s, s)
            assert len(loops) <= 1

            E_s_s = label_from_singleton_tr(loops)
            E_s_s_star = None if E_s_s is None else z3.Star(E_s_s)

            for p, q in itertools.product(predecessors, successors):
                # New label: E(p, q) + E(p, s)E(s, s)*E(s, q)
                p_q_trans = nfa.transitions_between(p, q)
                p_s_trans = nfa.transitions_between(p, s)
                s_q_trans = nfa.transitions_between(s, q)
                assert len(p_q_trans) <= 1 and len(p_s_trans) <= 1 and len(s_q_trans) <= 1

                E_p_q = label_from_singleton_tr(p_q_trans)
                E_p_s = label_from_singleton_tr(p_s_trans)
                assert E_p_s is not None
                E_s_q = label_from_singleton_tr(s_q_trans)
                assert E_s_q is not None

                # E(p, s)E(s, s)*
                regex = E_p_s if E_s_s_star is None else re_concat(E_p_s, E_s_s_star)
                regex = re_concat(regex, E_s_q)

                if E_p_q is not None:
                    regex = z3.Union(E_p_q, regex)

                nfa.delete_transitions(p_q_trans)
                nfa.add_transition(p, regex, q)

            nfa.delete_transitions(loops)
            nfa.delete_state(s)

        assert len(nfa.states) == 2

        if len(nfa.transitions) >= 1:
            p = nfa.initial_state
            q = nfa.final_state

            assert len(nfa.transitions_between(p, q)) == 1

            p_p_trans = nfa.transitions_between(p, p)
            p_q_trans = nfa.transitions_between(p, q)
            q_q_trans = nfa.transitions_between(q, q)

            E_p_q = label_from_singleton_tr(p_q_trans)
            assert E_p_q is not None
            E_p_p = label_from_singleton_tr(p_p_trans)
            E_q_q = label_from_singleton_tr(q_q_trans)

            # E(p,p)*E(p,q)E(q,q)*
            regex = E_p_q if E_p_p is None else re_concat(z3.Star(E_p_p), E_p_p)
            regex = regex if E_q_q is None else re_concat(regex, z3.Star(E_q_q))

            return regex
        else:
            return next(iter(nfa.transitions))[1]

    def right_linear_grammar_to_nfa(self, node: Union[str, Node]) -> NFA:
        node = self.str_to_nonterminal_node(node)
        self.assert_regular(node)
        assert self.grammar_type != GrammarType.LEFT_LINEAR

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
                            nfa.add_transition(current_state, self.tree_to_regex(child), next_state)
                        else:
                            sub_dfa = self.right_linear_grammar_to_nfa(child)
                            sub_dfa.substitute_final_state(next_state)
                            nfa.add_transitions(sub_dfa.transitions)
                            if (current_state, z3.Re(""), sub_dfa.initial_state) not in nfa.transitions:
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

        nfa.delete_isolated_states()

        for p, q in itertools.product(nfa.states, nfa.states):
            transitions = nfa.transitions_between(p, q)
            if len(transitions) >= 1:
                nfa.delete_transitions(transitions)
                nfa.add_transition(p, z3.Union(*[l for (_, l, _) in transitions]), q)

        return nfa

    def tree_to_regex(self, node: Union[str, Node]) -> z3.ReRef:
        if type(node) is str:
            node = self.grammar_graph.get_node(node)
            assert node

        if type(node) is TerminalNode:
            return z3.Re(node.symbol)

        assert type(node) is NonterminalNode
        assert self.grammar_graph.subgraph(node).is_tree()

        node: NonterminalNode
        choice_node: ChoiceNode

        union_nodes: List[z3.ReRef] = []
        for choice_node in node.children:
            children_regexes = [self.tree_to_regex(child) for child in choice_node.children]
            child_result = re_concat(*children_regexes)

            union_nodes.append(child_result)

        assert union_nodes

        if len(union_nodes) == 1:
            return union_nodes[0]
        else:
            return z3.Union(*union_nodes)

    def unwind_grammar(self, problematic_expansions: List[Tuple[Nonterminal, int, int]]) -> Grammar:
        """Unwinds the given problematic expansions up to self.max_num_expansions times. In the result, only
        terminal symbols or nonterminals that are root of a tree in the grammar graph are allowed."""

        result: Grammar = copy.deepcopy(self.grammar)

        while problematic_expansions:
            nonterminal, expansion_idx, nonterminal_idx = problematic_expansions.pop()

            expansion = result[nonterminal][expansion_idx]
            expansion_elements = split_expansion(expansion)
            nonterminal_to_expand = expansion_elements[nonterminal_idx]

            tree_like_symbols = {nonterminal for nonterminal in self.grammar.keys() if
                                 self.grammar_graph.subgraph(nonterminal).is_tree()}

            expansions = expand_nonterminals(self.grammar, nonterminal_to_expand, self.max_num_expansions,
                                             tree_like_symbols)

            if len(expansions) != 1:
                # Update expansion_idx references for problematic expansions with the same nonterminal
                other_problem: Tuple[Nonterminal, int, int]
                for other_problem in [problem for problem in list(problematic_expansions)
                                      if problem[0] == nonterminal and
                                         problem[1] >= expansion_idx]:
                    _, other_expansion_idx, other_nonterminal_idx = other_problem
                    if other_expansion_idx > expansion_idx:
                        problematic_expansions.remove((nonterminal, other_expansion_idx, other_nonterminal_idx))
                        problematic_expansions.append((nonterminal,
                                                    other_expansion_idx + len(expansions) - 1,
                                                    other_nonterminal_idx))
                    if other_expansion_idx == expansion_idx:
                        problematic_expansions.remove((nonterminal, other_expansion_idx, other_nonterminal_idx))
                        for i in range(len(expansions)):
                            problematic_expansions.append((nonterminal,
                                                        other_expansion_idx + i,
                                                        other_nonterminal_idx))

            new_expansions: List[str] = []

            for new_expansion in expansions:
                new_expansions.append("".join(expansion_elements[:nonterminal_idx] +
                                              [new_expansion] +
                                              expansion_elements[nonterminal_idx + 1:]))

                num_new_expansion_elements = 0 if not new_expansion else len(split_expansion(new_expansion))

                if num_new_expansion_elements != 1:
                    # Update nonterminal_idx references for problematic expansions with the same
                    # nonterminal and expansion index.
                    for other_problem in [problem for problem in list(problematic_expansions)
                                          if problem[0] == nonterminal and
                                             expansion_idx <= problem[1] <= expansion_idx + len(expansions) and
                                             problem[2] >= nonterminal_idx]:
                        _, other_expansion_idx, other_nonterminal_idx = other_problem
                        # assert other_nonterminal_idx > nonterminal_idx, \
                        #     "There should not be two problems for the same nonterminal occurrence"

                        problematic_expansions.remove((nonterminal, other_expansion_idx, other_nonterminal_idx))
                        problematic_expansions.append((nonterminal,
                                                    other_expansion_idx,
                                                    other_nonterminal_idx + num_new_expansion_elements - 1))

            result[nonterminal] = (result[nonterminal][:expansion_idx] +
                                   list(OrderedSet(new_expansions)) +
                                   result[nonterminal][expansion_idx + 1:])

        delete_unreachable(result)
        return result

    def assert_regular(self, node):
        """Asserts that the sub grammar at node is regular. Has a side effect: self.grammar_type is set!"""
        assert self.is_regular(node), f"The sub grammar at node {node.symbol} is not regular " \
                                      f"and cannot be converted to an NFA."

    def is_regular(self, nonterminal: Union[str, NonterminalNode]) -> bool:
        """
        Checks whether the language generated from "grammar" starting in "nonterminal" is regular.
        This is the case if all productions either are left- or rightlinear, with the exception that
        they may contain nonterminals that form a tree in the grammar. Those trivially represent
        regular expressions.

        :param nonterminal: A nonterminal within this grammar.
        :param call_seq: A tuple of already seen nodes, used to break infinite recursion.
        :return: True iff the language defined by the sublanguage of grammar's language when
                 starting in nonterminal is regular.
        """

        return not self.nonregular_expansions(nonterminal)

    def nonregular_expansions(self,
                              nonterminal: Union[str, NonterminalNode],
                              call_seq: Tuple = (),
                              problems: Union[None, Set[Tuple[Nonterminal, int, int]]] = None) -> \
            Set[Tuple[Nonterminal, int, int]]:
        """
        Returns pointers to expansions in a grammar which make the grammar non-regular. Those can then
        be unwound to convert the grammar into a regular grammar which represents a sub language.

        :param nonterminal: A nonterminal within this grammar.
        :param call_seq: A tuple of already seen nodes, used to break infinite recursion.
        :param problems: The so far encountered problematic expansions
        :return: A set of tuples, where each tuple represents a problematic expansion: A nonterminal (left-hand
                 side in the grammar), the index of the expansion where the problem occurs, and the index of
                 the problematic nonterminal within the expansion.
        """

        if not call_seq:
            self.grammar_type = GrammarType.UNDET

        if problems is None:
            problems = set([])

        if type(nonterminal) is str:
            nonterminal = self.grammar_graph.get_node(nonterminal)
            assert nonterminal
        nonterminal: NonterminalNode

        if nonterminal in call_seq:
            return problems

        # If the graph is a tree, we can easily create a regular expression with
        # concatenations and alternatives.

        if self.grammar_graph.subgraph(nonterminal).is_tree():
            return problems

        # If there is recursion, check if those children nonterminals with backlinks
        # are always at the left- or rightmost position, and all others are regular.

        choice_node: ChoiceNode
        for choice_node_index, choice_node in enumerate(nonterminal.children):
            found_backlink = False
            backlink_position = -1
            for index, child in enumerate(choice_node.children):
                if type(child) is TerminalNode:
                    continue

                child: NonterminalNode
                # if (self.grammar_graph.subgraph(child).is_tree() or
                #         (not self.grammar_graph.reachable(child, nonterminal) and
                #          self.nonregular_expansions(child, call_seq + (nonterminal,), problems))):
                if (self.grammar_graph.subgraph(child).is_tree() or
                        not self.grammar_graph.reachable(child, nonterminal)):
                    continue

                if found_backlink:
                    problems.add((nonterminal.symbol, choice_node_index, index))

                found_backlink = True
                backlink_position = index

            assert not found_backlink or backlink_position >= 0

            if found_backlink and len(choice_node.children) > 1:
                if backlink_position == 0:
                    if self.grammar_type == GrammarType.RIGHT_LINEAR:
                        problems.add((nonterminal.symbol, choice_node_index, backlink_position))
                    self.grammar_type = GrammarType.LEFT_LINEAR
                elif backlink_position == len(choice_node.children) - 1:
                    if self.grammar_type == GrammarType.LEFT_LINEAR:
                        problems.add((nonterminal.symbol, choice_node_index, backlink_position))
                    self.grammar_type = GrammarType.RIGHT_LINEAR
                else:
                    problems.add((nonterminal.symbol, choice_node_index, backlink_position))

        all_nontree_children_nonterminals = set([])
        for choice_node in nonterminal.children:
            for child in choice_node.children:
                if type(child) is NonterminalNode and not self.grammar_graph.subgraph(child).is_tree():
                    all_nontree_children_nonterminals.add(child)

        return set().union(*[self.nonregular_expansions(child, call_seq + (nonterminal,), problems)
                             for child in all_nontree_children_nonterminals])

    def str_to_nonterminal_node(self, node: Union[str, Node]) -> NonterminalNode:
        if type(node) is str:
            node = self.grammar_graph.get_node(node)
            assert node
        assert type(node) is NonterminalNode
        return node
