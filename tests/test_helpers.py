import copy
import logging
import unittest

import pytest
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import nonterminals, JSON_GRAMMAR
from fuzzingbook.Parser import EarleyParser

from grammar_to_regex.helpers import reverse_grammar, expand_nonterminals, delete_unreachable, \
    typed_canonical_to_grammar, grammar_to_typed_canonical


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

        expansions = expand_nonterminals(grammar, "<B>", 10)
        new_grammar = copy.deepcopy(grammar)

        for key, key_expansions in grammar.items():
            new_expansions = []
            for expansion in key_expansions:
                nonterminal_occurrences = nonterminals(expansion)
                if "<B>" not in nonterminal_occurrences:
                    new_expansions.append(expansion)
                    continue

                for new_expansion in expansions:
                    new_expansions.append(expansion.replace("<B>", "".join(list(map(str, new_expansion)))))

            new_grammar[key] = new_expansions

        delete_unreachable(new_grammar)
        self.assert_grammar_inclusion(new_grammar, grammar, allowed_failure_percentage=6)

    def test_grammar_type_conversion(self):
        self.assertEqual(JSON_GRAMMAR, typed_canonical_to_grammar(grammar_to_typed_canonical(JSON_GRAMMAR)))

    @pytest.mark.skip('This runs forever')
    def test_expand_json_nonterminal(self):
        logging.basicConfig(level=logging.DEBUG)

        expansions = expand_nonterminals(JSON_GRAMMAR, "<symbol-1>", 20)

        new_grammar = copy.deepcopy(JSON_GRAMMAR)

        for key, key_expansions in JSON_GRAMMAR.items():
            new_expansions = []
            for expansion in key_expansions:
                nonterminal_occurrences = nonterminals(expansion)
                if "<symbol-1>" not in nonterminal_occurrences:
                    new_expansions.append(expansion)
                    continue

                for new_expansion in expansions:
                    new_expansions.append(expansion.replace("<symbol-1>", "".join(list(map(str, new_expansion)))))

            new_grammar[key] = new_expansions

        delete_unreachable(new_grammar)
        self.assert_grammar_inclusion(new_grammar, JSON_GRAMMAR)

    def assert_grammar_inclusion(self,
                                 sub_grammar,
                                 grammar,
                                 runs: int = 1000,
                                 allowed_failure_percentage: int = 5,
                                 strict: bool = True):
        """
        Asserts that sub_grammar defines a language which is a strict subset of grammar.

        :param sub_grammar: The smaller grammar.
        :param grammar: The bigger grammar.
        :param runs: The number of test runs.
        :param allowed_failure_percentage: The maximum allowed percentage of samples from grammar
                                           that are not in sub_grammar.
        :param strict: True iff strict inclusion enforced (there has to be at least one counterexample for equality).
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

        self.assertLessEqual(fails, (allowed_failure_percentage / 100) * runs,
                             f"There were {(fails / runs) * 100:0.2f}% "
                             f"failures ({allowed_failure_percentage}% allowed)")

        if strict:
            self.assertGreater(fails, 0)


if __name__ == '__main__':
    unittest.main()
