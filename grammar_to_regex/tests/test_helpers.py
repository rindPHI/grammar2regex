import copy
import unittest

from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import nonterminals
from fuzzingbook.Parser import EarleyParser

from grammar_to_regex.helpers import reverse_grammar, expand_nonterminals, delete_unreachable


class TestHelpers(unittest.TestCase):
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

    def test_expand_nonterminals(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><C>"],
            "<B>": ["b<B>", "<C><B>", ""],
            "<C>": ["c"]
        }

        expansions = expand_nonterminals(grammar, "<B>", 10, {"<C>"})
        new_grammar = copy.deepcopy(grammar)

        for key, key_expansions in grammar.items():
            new_expansions = []
            for expansion in key_expansions:
                nonterminal_occurrences = nonterminals(expansion)
                if "<B>" not in nonterminal_occurrences:
                    new_expansions.append(expansion)
                    continue

                for new_expansion in expansions:
                    new_expansions.append(expansion.replace("<B>", new_expansion))

            new_grammar[key] = new_expansions

        delete_unreachable(new_grammar)
        self.assert_grammar_inclusion(new_grammar, grammar)

    def assert_grammar_inclusion(self, sub_grammar, grammar, runs: int = 1000, allowed_failure_percentage: int = 5):
        """
        Asserts that sub_grammar defines a language which is a strict subset of grammar.

        :param sub_grammar: The smaller grammar.
        :param grammar: The bigger grammar.
        :param allowed_failure_percentage: The maximum allowed percentage of samples from grammar
                                           that are not in sub_grammar.
        """
        fuzzer = GrammarCoverageFuzzer(sub_grammar)
        parser = EarleyParser(grammar)

        for _ in range(runs):
            inp = fuzzer.fuzz()
            try:
                list(parser.parse(inp))[0]
            except SyntaxError:
                self.fail(f"Input {inp} not in original language")

        fuzzer = GrammarCoverageFuzzer(grammar)
        parser = EarleyParser(sub_grammar)

        fails = 0
        for _ in range(runs):
            inp = fuzzer.fuzz()
            try:
                list(parser.parse(inp))[0]
            except SyntaxError:
                fails += 1

        # It's a reasonably big sublanguage, so there should be less than 5% of fails
        self.assertLess(fails, (allowed_failure_percentage / 100) * runs,
                        f"There were {(fails / runs) * 100:0.2f}% failures ({allowed_failure_percentage}% allowed)")
        # But it's reasonable to assume that there *are* fails
        self.assertGreater(fails, 0)


if __name__ == '__main__':
    unittest.main()
