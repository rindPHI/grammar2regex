import re
import typing
from typing import List, Dict, Callable, Union

import pydot
from fuzzingbook.Grammars import nonterminals, is_nonterminal

Nonterminal = str
Grammar = Dict[Nonterminal, List[str]]


class Node:
    def __init__(self, symbol: str):
        self.symbol = symbol

    def __hash__(self):
        return hash(self.symbol)

    def quote_symbol(self):
        return '"' + self.symbol.translate(str.maketrans({'"': r"\""})) + '"'


class NonterminalNode(Node):
    def __init__(self, symbol: str, children: List[Node]):
        super().__init__(symbol)
        self.children = children  # in fact, all children will be ChoiceNode instances.

    def __repr__(self):
        return f"NonterminalNode({self.quote_symbol()}, {repr(self.children)})"


class ChoiceNode(NonterminalNode):
    def __init__(self, symbol: str, children: List[Node]):
        super().__init__(symbol, children)

    def __repr__(self):
        return f"ChoiceNode({self.symbol}, {repr(self.children)})"


class TerminalNode(Node):
    def __init__(self, symbol: str, id: int):
        super().__init__(symbol)
        self.id = id

    def __repr__(self):
        return f"TerminalNode({self.quote_symbol()}, {self.id})"

    def __hash__(self):
        return hash((self.symbol, self.id))

    def quote_symbol(self):
        return Node(f"{self.symbol}-{self.id}").quote_symbol()


class GrammarGraph:
    def __init__(self, root):
        self.root = root

    def __repr__(self):
        return f"GrammarGraph({repr(self.root)})"

    def bfs(self, action: Callable[[Node], Union[None, bool]], start_node: Union[None, Node] = None):
        if start_node is None:
            start_node = self.root

        visited = [start_node]
        queue = [start_node]

        while queue:
            node = queue.pop(0)
            if action(node):
                return

            if issubclass(type(node), NonterminalNode):
                for child in node.children:
                    if child not in visited:
                        visited.append(child)
                        queue.append(child)

    @staticmethod
    def reachable(from_node: Node, to_node: Node) -> bool:
        graph = GrammarGraph(from_node)
        sources = graph.filter(lambda node: issubclass(type(node), NonterminalNode) and to_node in node.children)
        return len(sources) > 0

    def to_grammar(self):
        result: Grammar = {}

        def action(node: Node):
            nonlocal result
            if type(node) is TerminalNode or type(node) is ChoiceNode:
                return

            node: NonterminalNode
            choice_node: ChoiceNode
            productions = []
            for choice_node in node.children:
                productions.append("".join([child.symbol for child in choice_node.children]))

            result[node.symbol] = productions

        self.bfs(action)
        return result

    def subgraph(self, nonterminal: Union[NonterminalNode, str]):
        if type(nonterminal) is NonterminalNode:
            start_node = nonterminal
        else:
            start_node = self.get_node(nonterminal)

        if start_node.symbol == "<start>":
            return self

        root_node = NonterminalNode("<start>", [start_node])
        return GrammarGraph(root_node)

    def is_tree(self):
        # We cannot simply perform a BFS and return False if any child has already been
        # seen since we re-use nodes for the same nonterminal (they could be copied, but
        # I'd rather not do this).
        result = True

        def action(node: Node):
            nonlocal result
            if issubclass(type(node), NonterminalNode):
                if self.reachable(node, node):
                    result = False
                    return True

        self.bfs(action)
        return result

    def get_node(self, nonterminal: str) -> Union[None, NonterminalNode]:
        assert is_nonterminal(nonterminal)
        candidates = typing.cast(List[NonterminalNode],
                                 self.filter(lambda node: type(node) is NonterminalNode and node.symbol == nonterminal))
        if not candidates:
            return None
        assert len(candidates) == 1
        return candidates[0]

    def filter(self, f: Callable[[Node], bool]) -> List[Node]:
        result: List[Node] = []

        def action(node: Node):
            nonlocal result
            if f(node):
                result.append(node)

        self.bfs(action)
        return result

    def to_dot(self):
        graph = pydot.Dot('GrammarGraph', graph_type='digraph')

        def action(node: Node):
            if type(node) is TerminalNode:
                graph.add_node(pydot.Node(node.quote_symbol(), label=Node(node.symbol).quote_symbol(), shape="box"))
            elif type(node) is ChoiceNode:
                graph.add_node(pydot.Node(node.quote_symbol(), shape="diamond"))
            else:
                graph.add_node(pydot.Node(node.quote_symbol(), shape="circle"))

            if issubclass(type(node), NonterminalNode):
                node: NonterminalNode
                for nr, child in enumerate(node.children):
                    graph.add_edge(pydot.Edge(node.quote_symbol(), child.quote_symbol(), label=f"<{nr + 1}>"))

        self.bfs(action)
        return graph.to_string()

    @staticmethod
    def from_grammar(grammar: Grammar):
        nonterminal_nodes: Dict[str, NonterminalNode] = {}
        terminal_ids: Dict[str, int] = {}

        def recurse(label: str) -> Node:
            nonlocal nonterminal_nodes, terminal_ids

            if not is_nonterminal(label):
                terminal_id = terminal_ids.setdefault(label, 1)
                terminal_ids[label] = terminal_id + 1
                return TerminalNode(label, terminal_id)

            if label in nonterminal_nodes:
                return nonterminal_nodes[label]

            children_nodes = []
            new_node = NonterminalNode(label, children_nodes)
            nonterminal_nodes[label] = new_node

            for nr, expansion in enumerate(grammar[label]):
                expansion_elements = split_expansion(nonterminals(expansion), expansion)
                expansion_children_nodes = []
                for elem in expansion_elements:
                    if elem == label:
                        expansion_children_nodes.append(new_node)
                    else:
                        expansion_children_nodes.append(recurse(elem))
                children_nodes.append(ChoiceNode(f"{label}-choice-{nr + 1}", expansion_children_nodes))

            return new_node

        return GrammarGraph(recurse("<start>"))


def split_expansion(nonterminal_symbols: List[str], expansion: str) -> List[str]:
    if not nonterminal_symbols:
        return [expansion]

    for nonterminal_symbol in nonterminal_symbols:
        expansion = re.sub(f"({re.escape(nonterminal_symbol)})", '[cut]\\1[cut]', expansion)

    return [s for s in expansion.split("[cut]") if s]
