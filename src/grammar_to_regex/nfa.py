import copy
from typing import Tuple, Dict, TypeVar, Union, Generator, Set, Iterable

import pydot
from orderedset import OrderedSet

State = TypeVar('State')
Letter = TypeVar('Letter')
Transition = Tuple[State, Letter, State]


class NFA:
    def __init__(self,
                 states: Tuple[State, ...] = (),
                 initial_state: Union[State, None] = None,
                 final_state: Union[State, None] = None,
                 transitions: Union[Set[Transition], None] = None):
        self.states = OrderedSet(states)
        self.initial_state = initial_state
        self.final_state = final_state
        self.transitions: Set[Transition] = set([]) if transitions is None else transitions

        self.successor_map: Dict[State, Set[State]] = dict([])
        self.predecessor_map: Dict[State, Set[State]] = dict([])

        self.initialize_neighborhood()

    def initialize_neighborhood(self):
        for state in self.states:
            self.successor_map[state] = set([])
            self.predecessor_map[state] = set([])

        for (from_state, letter, to_state) in self.transitions:
            self.successor_map[from_state].add(to_state)
            self.predecessor_map[to_state].add(from_state)

    def predecessors(self, state):
        result = self.predecessor_map[state]
        assert result == set([p for (p, _, q) in self.transitions if q == state])
        return result

    def successors(self, state):
        result = self.successor_map[state]
        assert result == set([q for (p, _, q) in self.transitions if p == state])
        return result

    def next_free_state(self, generator: Generator[State, None, None]):
        for state in generator:
            if state in self.states:
                continue
            return state

    def add_state(self, state: State, initial=False, final=False):
        assert state not in self.states
        self.states.add(state)
        self.successor_map.setdefault(state, set([]))
        self.predecessor_map.setdefault(state, set([]))

        if initial:
            self.initial_state = state
        if final:
            self.final_state = state

    def delete_state(self, state: State):
        assert state != self.initial_state
        assert state != self.final_state

        self.delete_transitions([(s1, _, s2) for (s1, _, s2) in self.transitions if state in (s1, s2)])
        self.states.remove(state)

    def delete_isolated_states(self):
        self.states = OrderedSet([state for state in self.states if any(
            [(s1, l, s2) for (s1, l, s2) in self.transitions if state in (s1, s2)]
        )])

    def transitions_between(self, p, q):
        return [(_p, l, _q) for (_p, l, _q) in self.transitions if _p == p and _q == q]

    def substitute_states(self, subst_map: Dict[State, State]) -> 'NFA':
        initial_state = subst_map.get(self.initial_state, self.initial_state)
        final_state = subst_map.get(self.final_state, self.final_state)

        states = copy.deepcopy(self.states)
        for state in subst_map:
            states.remove(state)
            states.add(subst_map[state])

        transitions = {
            (subst_map.get(from_state, from_state), letter, subst_map.get(to_state, to_state))
            for from_state, letter, to_state in self.transitions
        }

        return NFA(tuple(states), initial_state, final_state, transitions)

    def substitute_final_state(self, new_final_state) -> 'NFA':
        return self.substitute_states({self.final_state: new_final_state})

    def add_transition(self, from_state: State, letter: Letter, to_state: State, safe: bool = True):
        # assert (from_state, letter) not in self.transitions  # <-- for DFA
        if safe:
            assert (from_state, letter, to_state) not in self.transitions
        self.transitions.add((from_state, letter, to_state))
        self.successor_map[from_state].add(to_state)
        self.predecessor_map[to_state].add(from_state)

    def add_transitions(self, transitions: Iterable[Transition], safe: bool = True):
        for transition in transitions:
            self.add_transition(*transition, safe)

    def delete_transition(self, from_state: State, letter: Letter, to_state: State):
        assert (from_state, letter, to_state) in self.transitions
        self.transitions.remove((from_state, letter, to_state))

        if not any((s1, _, s2) for (s1, _, s2) in self.transitions if s1 == from_state and s2 == to_state):
            self.successor_map[from_state].remove(to_state)
            self.predecessor_map[to_state].remove(from_state)

    def delete_transitions(self, transitions: Iterable[Transition]):
        for transition in transitions:
            self.delete_transition(*transition)

    def reverse(self):
        """Reverses the transitions of the NFA. Useful for conversion of a left-linear grammar to regex."""
        new_transitions = {(to_state, letter, from_state) for (from_state, letter, to_state) in self.transitions}
        return NFA(states=tuple(self.states),
                   initial_state=self.final_state,
                   final_state=self.initial_state,
                   transitions=new_transitions)

    def to_dot(self):
        graph = pydot.Dot('DFA', graph_type='digraph')

        init = pydot.Node("init", label="", shape="point")
        graph.add_node(init)
        graph.add_edge(pydot.Edge(init, self.initial_state))

        for state in self.states:
            shape = "doublecircle" if state == self.final_state else "circle"
            graph.add_node(pydot.Node(state, shape=shape))

        for from_state, letter, to_state in self.transitions:
            graph.add_edge(pydot.Edge(from_state, to_state, label=str(letter)))

        return graph.to_string()
