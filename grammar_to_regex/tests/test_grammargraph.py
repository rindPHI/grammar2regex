import unittest

from fuzzingbook.Grammars import JSON_GRAMMAR, US_PHONE_GRAMMAR

from grammar_to_regex.grammargraph import GrammarGraph
from grammar_to_regex.helpers import reverse_grammar


class TestRegularityChecker(unittest.TestCase):

    # def test_todot(self):
    #     graph = GrammarGraph.from_grammar(JSON_GRAMMAR)
    #     print(graph.to_dot())

    def test_reachability_and_filter(self):
        graph = GrammarGraph.from_grammar(JSON_GRAMMAR)

        element_node = graph.get_node("<element>")
        self.assertTrue(graph.reachable(element_node, element_node))

        value_node = graph.get_node("<value>")
        self.assertTrue(graph.reachable(value_node, value_node))
        self.assertTrue(graph.reachable(element_node, value_node))

        int_node = graph.get_node("<int>")
        self.assertTrue(graph.reachable(value_node, int_node))
        self.assertTrue(graph.reachable(element_node, int_node))
        self.assertFalse(graph.reachable(int_node, int_node))

    def test_to_grammar(self):
        graph = GrammarGraph.from_grammar(JSON_GRAMMAR)
        self.assertEqual(JSON_GRAMMAR, graph.to_grammar())

    def test_is_tree(self):
        graph = GrammarGraph.from_grammar(JSON_GRAMMAR)
        self.assertFalse(graph.is_tree())
        self.assertTrue(graph.subgraph("<character>").is_tree())
        self.assertTrue(graph.subgraph("<digit>").is_tree())
        self.assertFalse(graph.subgraph("<digits>").is_tree())
        self.assertTrue(graph.subgraph("<sign>").is_tree())
        self.assertFalse(graph.subgraph("<start>").is_tree())

    def test_is_tree_2(self):
        graph = GrammarGraph.from_grammar(US_PHONE_GRAMMAR)
        self.assertTrue(graph.subgraph("<exchange>").is_tree())
        self.assertTrue(graph.subgraph("<start>").is_tree())

    def test_reverse(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><C>"],
            "<B>": ["b<B>", ""],
            "<C>": ["c"]
        }

        reversed_grammar = {
            "<start>": ["<A>"],
            "<A>": ["<C><B>a"],
            "<B>": ["<B>b", ""],
            "<C>": ["c"]
        }

        self.assertEqual(reversed_grammar, reverse_grammar(grammar))


if __name__ == '__main__':
    unittest.main()
