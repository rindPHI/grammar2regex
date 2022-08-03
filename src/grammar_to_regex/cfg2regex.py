import copy
import itertools
import logging
from enum import Enum
from typing import Dict, List, Tuple, Generator, Optional, cast

import z3
from grammar_graph.gg import GrammarGraph, NonterminalNode, ChoiceNode, TerminalNode, Node
from orderedset import OrderedSet

from grammar_to_regex.helpers import reverse_grammar, expand_nonterminals, delete_unreachable, \
    grammar_to_typed_canonical, GrammarElem, str2grammar_elem, Nonterminal, typed_canonical_to_grammar, \
    consecutive_numbers
from grammar_to_regex.nfa import NFA, Transition
from grammar_to_regex.regex import Regex, concat, Star, Union, Singleton, regex_to_z3, union, Range, Concat, star, \
    epsilon
from grammar_to_regex.type_defs import Grammar, NonterminalType


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
    def __init__(self, grammar: Grammar, max_num_expansions: int = 10, compress_unions: bool = False):
        """
        :param grammar: The underlying grammar.
        :param max_num_expansions: For non-regular (sub) grammars, we can unwind problematic nonterminals in
                                   expansions. This parameter sets a depth bound on the number of unwindings.
        :param compress_unions: If True, unions of single-char regexes will be compressed to range expressions.
        """

        self.grammar: Grammar = grammar
        self.max_num_expansions = max_num_expansions
        self.compress_unions = compress_unions

        self.grammar_type: GrammarType = GrammarType.UNDET
        self.grammar_graph: GrammarGraph = GrammarGraph.from_grammar(grammar)

        self.regularity_cache: Dict[str, bool] = {}
        self.regularity_cache_created_for: Grammar = grammar

        self.nfa_cache: Dict[str, NFA] = {}
        self.nfa_cache_created_for: Grammar = grammar
        self.state_gen = state_generator("q")

        self.logger = logging.getLogger("RegexConverter")

    def to_regex(self, node_symbol: str | Node, convert_to_z3=True) -> z3.ReRef | Regex:
        old_grammar = copy.deepcopy(self.grammar)
        self.grammar_graph = self.grammar_graph.subgraph(node_symbol)
        self.grammar = self.grammar_graph.to_grammar()

        node = self.str_to_nonterminal_node(node_symbol)
        self.logger.info("Computing nonregular expansions.")
        problematic_expansions: OrderedSet[Tuple[NonterminalType, int, int]] = self.nonregular_expansions(node)

        if problematic_expansions:
            self.logger.info(f"Grammar found to be non-regular, unwinding {len(problematic_expansions)} expansion "
                             f"elements to depth {self.max_num_expansions}")
            unwound_grammar = self.unwind_grammar(problematic_expansions)
            self.grammar = unwound_grammar
            self.grammar_graph = GrammarGraph.from_grammar(unwound_grammar)
            # pyperclip.copy(self.grammar_graph.to_dot())
            self.logger.info("Done unwinding.")
        else:
            self.logger.info("Grammar is regular.")

        if self.grammar_graph.subgraph(node).is_tree():
            result = self.tree_to_regex(node)

        # NOTE: We have to use node_symbol below, because node is still from the old,
        #       not unwound / nonregular grammar graph.
        elif self.grammar_type == GrammarType.LEFT_LINEAR:
            result = self.left_linear_grammar_to_regex(node_symbol)
        else:
            result = self.right_linear_grammar_to_regex(node_symbol)

        self.grammar = old_grammar
        self.grammar_graph = GrammarGraph.from_grammar(self.grammar)

        if self.compress_unions:
            result = compress_unions(result)

        return result if not convert_to_z3 else regex_to_z3(result)

    def left_linear_grammar_to_regex(self, node_symbol: str | Node) -> Regex:
        node = self.str_to_nonterminal_node(node_symbol)
        self.assert_regular(node)
        assert self.grammar_type == GrammarType.LEFT_LINEAR

        self.logger.info("Reversing left-linear grammar for NFA conversion.")
        old_grammar_graph = self.grammar_graph
        self.grammar_graph = GrammarGraph.from_grammar(reverse_grammar(self.grammar))
        # Grammar represented by graph is right-linear now

        nfa = self.right_linear_grammar_to_nfa(node_symbol)
        assert nfa is not None

        self.logger.info("Reversing NFA created for reversed left-linear grammar")
        nfa = nfa.reverse()

        self.grammar_graph = old_grammar_graph
        self.logger.info(f"Converting NFA of sub grammar for {node_symbol} to regex")

        return self.nfa_to_regex(nfa)

    def right_linear_grammar_to_regex(self, node: str | Node) -> Regex:
        node = self.str_to_nonterminal_node(node)
        self.assert_regular(node)
        assert self.grammar_type != GrammarType.LEFT_LINEAR

        nfa = self.right_linear_grammar_to_nfa(node)
        assert nfa is not None

        self.logger.info(f"Converting NFA of sub grammar for {node.symbol} to regex")
        return self.nfa_to_regex(nfa)

    def nfa_to_regex(self, nfa: Optional[NFA]) -> Regex:
        assert not [state for state in nfa.states if not any(
            [(s1, l, s2) for (s1, l, s2) in nfa.transitions if state in (s1, s2)]
        )], f"Found isolated states!"

        def label_from_singleton_tr(transitions: List[Transition]) -> Optional[Regex]:
            return None if not transitions else transitions[0][1]

        # It's much faster if we start eliminating states with few predecessors and successors
        intermediate_states = [state for state in nfa.states if state not in (nfa.initial_state, nfa.final_state)]
        intermediate_states = sorted(
            intermediate_states,
            key=lambda s: len(nfa.predecessors(s)) + len(nfa.successors(s)))

        while len(intermediate_states) > 0:
            s = intermediate_states[0]

            predecessors = [p for p in nfa.predecessors(s) if p != s]
            successors = [q for q in nfa.successors(s) if q != s]
            loops = nfa.transitions_between(s, s)
            assert len(loops) <= 1

            self.logger.debug(f"Eliminating state {s} ({len(predecessors)} preds / {len(successors)} succs), "
                              f"{len(nfa.states)} states left")

            E_s_s = label_from_singleton_tr(loops) or epsilon()

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

                # E(p, s)E(s, s)*E(s, q)
                regex = concat(E_p_s, star(E_s_s), E_s_q)

                if E_p_q is not None:
                    regex = union(E_p_q, regex)

                nfa.delete_transitions(p_q_trans)
                nfa.add_transition(p, regex, q)

            nfa.delete_transitions(loops)
            nfa.delete_state(s)
            intermediate_states.remove(s)

        assert len(nfa.states) == 2

        if len(nfa.transitions) >= 1:
            p = nfa.initial_state
            q = nfa.final_state

            assert len(nfa.transitions_between(p, q)) == 1

            p_p_trans = nfa.transitions_between(p, p)
            p_q_trans = nfa.transitions_between(p, q)
            q_q_trans = nfa.transitions_between(q, q)

            E_p_q = label_from_singleton_tr(p_q_trans) or epsilon()
            assert E_p_q is not None
            E_p_p = label_from_singleton_tr(p_p_trans) or epsilon()
            E_q_q = label_from_singleton_tr(q_q_trans) or epsilon()

            # E(p,p)*E(p,q)E(q,q)*
            return concat(star(E_p_p), E_p_q, star(E_q_q))
        else:
            return next(iter(nfa.transitions))[1]

    def right_linear_grammar_to_nfa(self, node: str | Node) -> NFA:
        node = self.str_to_nonterminal_node(node)
        self.assert_regular(node)

        if self.nfa_cache_created_for == self.grammar and node.symbol in self.nfa_cache:
            return self.nfa_cache[node.symbol]
        elif self.nfa_cache_created_for != self.grammar:
            self.nfa_cache_created_for = self.grammar
            self.nfa_cache = {}

        self.logger.info(f"Converting sub grammar for nonterminal {node.symbol} to NFA")

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
                assert children, "Choice node has no children, but always should have."
                current_state = node.quote_symbol()

                for child in children[0:-1]:
                    next_state = nfa.next_free_state(self.state_gen)
                    nfa.add_state(next_state)

                    if isinstance(child, TerminalNode):
                        nfa.add_transition(current_state, Singleton(child.symbol), next_state)
                    else:
                        assert isinstance(child, NonterminalNode)
                        if self.grammar_graph.subgraph(child).is_tree():
                            nfa.add_transition(current_state, self.tree_to_regex(child), next_state)
                        else:
                            if child in self.nfa_cache:
                                sub_nfa = self.nfa_cache[child.symbol]
                            else:
                                sub_nfa = self.right_linear_grammar_to_nfa(child)
                                self.nfa_cache[child.symbol] = sub_nfa

                            sub_nfa = sub_nfa.substitute_states({
                                state: nfa.next_free_state(self.state_gen)
                                for state in sub_nfa.states
                                if state in nfa.states and state != sub_nfa.final_state
                            } | {sub_nfa.final_state: next_state})

                            for state in sub_nfa.states:
                                if state not in nfa.states:
                                    nfa.add_state(state)

                            nfa.add_transitions(sub_nfa.transitions)

                            if (current_state, epsilon(), sub_nfa.initial_state) not in nfa.transitions:
                                nfa.add_transition(current_state, epsilon(), sub_nfa.initial_state)

                    current_state = next_state

                child = children[-1]

                if type(child) is TerminalNode:
                    nfa.add_transition(current_state, Singleton(child.symbol), final_state)
                else:
                    nfa.add_transition(current_state, epsilon(), child.quote_symbol(), safe=False)
                    if child not in visited:
                        visited.append(child)
                        queue.append(child)

        nfa.delete_isolated_states()

        # Bundle transitions between the same states
        # for p, q in itertools.product(nfa.states, nfa.states):
        # TODO: Might no longer be necessary due to sub-NFA renaming?
        for p, q in [(p, q) for p, _, q in nfa.transitions]:
            transitions = nfa.transitions_between(p, q)
            if len(transitions) >= 1:
                nfa.delete_transitions(transitions)
                nfa.add_transition(p, union(*[l for (_, l, _) in transitions]), q)

        self.nfa_cache[node.symbol] = nfa

        return nfa

    def tree_to_regex(self, node: str | Node) -> Regex:
        if type(node) is str:
            node = self.grammar_graph.get_node(node)
            assert node

        if isinstance(node, TerminalNode):
            return Singleton(node.symbol)

        assert type(node) is NonterminalNode
        assert self.grammar_graph.subgraph(node).is_tree()

        node: NonterminalNode
        choice_node: ChoiceNode

        union_nodes: List[Regex] = []
        for choice_node in node.children:
            children_regexes = [self.tree_to_regex(child) for child in choice_node.children]
            child_result = concat(*children_regexes)

            union_nodes.append(child_result)

        return union(*union_nodes)

    def unwind_grammar(self,
                       problematic_expansions_str: OrderedSet[Tuple[NonterminalType, int, int]]) -> Grammar:
        """Unwinds the given problematic expansions up to self.max_num_expansions times. In the result, only
        terminal symbols or nonterminals that are root of a tree in the grammar graph are allowed."""

        canonical_grammar: Dict[GrammarElem, List[List[GrammarElem]]] = \
            grammar_to_typed_canonical(self.grammar)
        replacements: Dict[GrammarElem, List[List[GrammarElem]]] = dict([])
        problematic_expansions: OrderedSet[Tuple[GrammarElem, int, int]] = \
            OrderedSet([(str2grammar_elem(nonterminal_str), idx_1, idx_2)
                        for nonterminal_str, idx_1, idx_2 in problematic_expansions_str])

        allowed_symbols = {str(nonterminal) for nonterminal in self.grammar.keys() if
                           # self.grammar_graph.subgraph(nonterminal).is_tree()
                           self.is_regular(str(nonterminal))
                           }

        while problematic_expansions:
            nonterminal: Nonterminal
            expansion_idx: int
            nonterminal_idx: int
            nonterminal, expansion_idx, nonterminal_idx = problematic_expansions.pop()

            expansion = canonical_grammar[nonterminal][expansion_idx]
            nonterminal_to_expand: Nonterminal = cast(Nonterminal, expansion[nonterminal_idx])
            assert isinstance(nonterminal_to_expand, Nonterminal)
            assert str(nonterminal_to_expand) not in allowed_symbols, f"Symbol {nonterminal_to_expand} is " \
                                                                      f"an allowed symbol and shouldn't be " \
                                                                      f"expanded!"

            self.logger.info(f"Unwinding nonterminal {nonterminal_idx + 1} ({nonterminal_to_expand}) in "
                             f"{expansion_idx + 1}. expansion rule of {nonterminal}")

            expansions: List[List[GrammarElem]]
            if nonterminal_to_expand in replacements:
                expansions = replacements[nonterminal_to_expand]
            else:
                self.logger.debug(f"Expanding nonterminal {nonterminal_to_expand}")
                expansions = expand_nonterminals(self.grammar,
                                                 str(nonterminal_to_expand),
                                                 self.max_num_expansions,
                                                 allowed_symbols)
                assert expansions
                replacements[nonterminal_to_expand] = expansions

            new_expansions: List[List[GrammarElem]] = list([])

            for idx, new_expansion in enumerate(expansions):
                to_add = expansion[:nonterminal_idx] + new_expansion + expansion[nonterminal_idx + 1:]
                if to_add not in new_expansions:
                    new_expansions.append(to_add)

            canonical_grammar[nonterminal] = (canonical_grammar[nonterminal][:expansion_idx] +
                                              new_expansions +
                                              canonical_grammar[nonterminal][expansion_idx + 1:])

            # Update remaining problem pointers
            old_problematic_expansions = OrderedSet(problematic_expansions)
            for idx, new_expansion in enumerate(expansions):
                for other_expansion_index, other_nonterminal_index in [
                    (other_expansion_index, other_nonterminal_index)
                    for (other_nonterminal, other_expansion_index, other_nonterminal_index)
                    in old_problematic_expansions
                    if nonterminal == other_nonterminal
                    if other_expansion_index >= expansion_idx
                ]:
                    if (nonterminal, other_expansion_index, other_nonterminal_index) in problematic_expansions:
                        problematic_expansions.remove((nonterminal, other_expansion_index, other_nonterminal_index))

                    new_expansion_index = other_expansion_index + idx
                    assert new_expansion_index < len(canonical_grammar[nonterminal])

                    if other_nonterminal_index >= nonterminal_idx:
                        new_nonterminal_index = other_nonterminal_index + len(new_expansion) - 1
                    else:
                        new_nonterminal_index = other_nonterminal_index

                    assert new_nonterminal_index < len(canonical_grammar[nonterminal][new_expansion_index]), \
                        "Invalid nonterminal index produced."

                    new_problemantic_element = \
                        canonical_grammar[nonterminal][new_expansion_index][new_nonterminal_index]
                    assert type(new_problemantic_element) is Nonterminal, \
                        f"Symbol {new_problemantic_element} is " \
                        f"a terminal symbol and can thus not be problematic."
                    assert str(new_problemantic_element) not in allowed_symbols, \
                        f"Symbol {new_problemantic_element} is an " \
                        f"allowed nonterminal and can thus not be problematic."

                    problematic_expansions.add((nonterminal, new_expansion_index, new_nonterminal_index))

        result = typed_canonical_to_grammar(canonical_grammar)
        delete_unreachable(result)
        return result

    def assert_regular(self, node):
        """Asserts that the sub grammar at node is regular. Has a side effect: self.grammar_type is set!"""
        assert self.is_regular(node), f"The sub grammar at node {node.symbol} is not regular " \
                                      f"and cannot be converted to an NFA."

    def is_regular(self, nonterminal: str | NonterminalNode) -> bool:
        """
        Checks whether the language generated from "grammar" starting in "nonterminal" is regular.
        This is the case if all productions either are left- or rightlinear, with the exception that
        they may contain nonterminals that form a tree in the grammar. Those trivially represent
        regular expressions.

        :param nonterminal: A nonterminal within this grammar.
        :return: True iff the language defined by the sublanguage of grammar's language when
                 starting in nonterminal is regular.
        """

        nonterminal_str = nonterminal if type(nonterminal) is str else nonterminal.symbol

        if self.regularity_cache_created_for == self.grammar and nonterminal_str in self.regularity_cache:
            return self.regularity_cache[nonterminal_str]
        elif self.regularity_cache_created_for != self.grammar:
            self.regularity_cache_created_for = self.grammar
            self.regularity_cache = {}

        result = not self.nonregular_expansions(nonterminal)

        self.regularity_cache[nonterminal_str] = result

        return result

    def nonregular_expansions(self,
                              nonterminal: str | NonterminalNode,
                              call_seq: Tuple = (),
                              problems: Optional[OrderedSet[Tuple[NonterminalType, int, int]]] = None) -> \
            OrderedSet[Tuple[NonterminalType, int, int]]:
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
            problems = OrderedSet([])

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

        all_nontree_children_nonterminals = OrderedSet([])
        for choice_node in nonterminal.children:
            for child in choice_node.children:
                if type(child) is NonterminalNode and not self.grammar_graph.subgraph(child).is_tree():
                    all_nontree_children_nonterminals.add(child)

        result = OrderedSet()

        for child_result in [self.nonregular_expansions(child, call_seq + (nonterminal,), problems)
                             for child in all_nontree_children_nonterminals]:
            result |= child_result

        return result

    def str_to_nonterminal_node(self, node: str | Node) -> NonterminalNode:
        if type(node) is str:
            node = self.grammar_graph.get_node(node)
            assert node
        assert type(node) is NonterminalNode
        return node


def compress_unions(regex: Regex) -> Regex:
    # We assume that all unions are flattened, i.e., there are no unions directly nested inside unions
    if isinstance(regex, Union):
        # Compress single-char unions to ranges
        char_nodes = [
            child for child in regex.children
            if isinstance(child, Singleton)
        ]

        others = [compress_unions(child) for child in regex.children if child not in char_nodes]

        chars = OrderedSet([char_node.child for char_node in char_nodes])
        # NOTE: In some cases, string sequences that are longer than one char can appear in chars;
        #       for an XML grammar, e.g., escaped sequences like &quot; might appear.
        char_codes = sorted([ord(char) for char in chars if len(char) == 1])
        consecutive_char_codes = consecutive_numbers(char_codes)

        union_nodes = [
            Singleton(chr(group[0])) if len(group) == 1
            else Range(chr(group[0]), chr(group[-1]))
            for group in consecutive_char_codes
        ]
        union_nodes += others

        # NOTE: `longer_str` can also include the empty string.
        union_nodes.extend([Singleton(longer_str) for longer_str in chars if len(longer_str) != 1])

        return union(*union_nodes)

    if isinstance(regex, Star):
        return Star(compress_unions(regex.child))

    if isinstance(regex, Concat):
        return concat(*[compress_unions(child) for child in regex.children])

    return regex
