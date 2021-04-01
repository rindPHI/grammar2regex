from typing import Tuple, Dict, TypeVar, Union, List, Generator, Set

import pydot
import z3
from orderedset import OrderedSet

State = TypeVar('State')
Letter = TypeVar('Letter')


class NFA:
    def __init__(self,
                 states: Tuple[State, ...] = (),
                 initial_state: Union[State, None] = None,
                 final_state: Union[State, None] = None,
                 transitions: Union[Set[Tuple[State, Letter, State]], None] = None):
        self.states = OrderedSet(states)
        self.initial_state = initial_state
        self.final_state = final_state
        self.transitions: Set[Tuple[State, Letter, State]] = set([]) if transitions is None else transitions

        self.successor_map: Dict[State, List[State]] = dict([])
        self.predecessor_map: Dict[State, List[State]] = dict([])

        self.update_neighborhood()

    def update_neighborhood(self):
        for (from_state, letter, to_state) in self.transitions:
            self.successor_map.setdefault(from_state, [])
            self.successor_map[from_state].append(to_state)

            self.predecessor_map.setdefault(to_state, [])
            self.predecessor_map[to_state].append(from_state)

    def next_free_state(self, generator: Generator[State, None, None]):
        for state in generator:
            if state in self.states:
                continue
            return state

    def add_state(self, state: State, initial=False, final=False):
        assert state not in self.states
        self.states.add(state)

        if initial:
            self.initial_state = state
        if final:
            self.final_state = state

    def substitute_final_state(self, new_final_state):
        old_final_state = self.final_state
        self.final_state = new_final_state

        for from_state, letter, to_state in self.transitions:
            if to_state == old_final_state:
                self.transitions.remove((from_state, letter, to_state))
                self.add_transition(from_state, letter, new_final_state)

    def add_transition(self, from_state: State, letter: Letter, to_state: State):
        # assert (from_state, letter) not in self.transitions  # <-- for DFA
        assert (from_state, letter, to_state) not in self.transitions
        self.transitions.add((from_state, letter, to_state))
        self.update_neighborhood()

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
