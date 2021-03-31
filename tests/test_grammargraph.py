import unittest

from fuzzingbook.Grammars import JSON_GRAMMAR

from grammargraph import GrammarGraph


class TestRegularityChecker(unittest.TestCase):

    def test_reachability_and_filter(self):
        graph = GrammarGraph.from_grammar(JSON_GRAMMAR)
        # print(graph.to_dot())

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

if __name__ == '__main__':
    unittest.main()
