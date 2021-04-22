import logging
import unittest

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import US_PHONE_GRAMMAR, JSON_GRAMMAR
from fuzzingbook.Parser import EarleyParser
from string_sampler.sampler import StringSampler, StringSamplerConfiguration

from grammar_to_regex.cfg2regex import RegexConverter, GrammarType, Grammar

RIGHT_LINEAR_TOY_GRAMMAR = \
    {"<start>": ["<A>"],
     "<A>": ["a<number><B>", "b<A>", "b"],
     "<B>": ["a<C>", "b<B>"],
     "<C>": ["a<A>", "b<C>"],
     "<number>": ["1", "2", "3"]
     }


class TestRegexConverter(unittest.TestCase):
    def test_toy_grammar_regularity(self):
        grammar = {"<start>": ["<A>"],
                   "<A>": ["<B>a", "<A>b", "b"],
                   "<B>": ["<C>a", "<B>b"],
                   "<C>": ["<A>a", "<C>b"]
                   }
        checker = RegexConverter(grammar)
        self.assertTrue(checker.is_regular("<start>"))

    def test_us_phone_grammar_regularity(self):
        checker = RegexConverter(US_PHONE_GRAMMAR)
        self.assertTrue(checker.is_regular("<start>"))
        self.assertEqual(GrammarType.UNDET, checker.grammar_type)

    def test_json_grammar_regularity(self):
        checker = RegexConverter(JSON_GRAMMAR)
        self.assertFalse(checker.is_regular("<start>"))
        self.assertFalse(checker.is_regular("<value>"))
        self.assertFalse(checker.is_regular("<member>"))
        self.assertFalse(checker.is_regular("<symbol>"))
        self.assertFalse(checker.is_regular("<elements>"))

        self.assertTrue(checker.is_regular("<int>"))
        self.assertEqual(checker.grammar_type, GrammarType.RIGHT_LINEAR)
        self.assertTrue(checker.is_regular("<exp>"))
        self.assertEqual(checker.grammar_type, GrammarType.RIGHT_LINEAR)
        self.assertTrue(checker.is_regular("<characters>"))
        self.assertEqual(checker.grammar_type, GrammarType.RIGHT_LINEAR)
        self.assertTrue(checker.is_regular("<string>"))
        self.assertEqual(checker.grammar_type, GrammarType.RIGHT_LINEAR)

    def test_us_phone_grammar_to_regex_from_tree(self):
        checker = RegexConverter(US_PHONE_GRAMMAR)
        regex = checker.tree_to_regex("<start>")

        self.assertEqual(z3.sat, self.smt_check(z3.InRe("(200)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(000)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(200)200-000", regex)))

    def test_us_phone_grammar_to_regex(self):
        logging.basicConfig(level=logging.INFO)
        checker = RegexConverter(US_PHONE_GRAMMAR)
        regex = checker.right_linear_grammar_to_regex("<start>")

        self.check_grammar_regex_equivalence(US_PHONE_GRAMMAR, regex)

    def test_toy_grammar_to_nfa(self):
        checker = RegexConverter(RIGHT_LINEAR_TOY_GRAMMAR)
        checker.right_linear_grammar_to_nfa("<A>")
        # No Exception

    def test_toy_grammar_to_regex(self):
        checker = RegexConverter(RIGHT_LINEAR_TOY_GRAMMAR)
        regex = checker.right_linear_grammar_to_regex("<A>")

        self.check_grammar_regex_equivalence(RIGHT_LINEAR_TOY_GRAMMAR, regex)

    def test_simple_toy_grammar_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><C>"],
            "<B>": ["b<B>", ""],
            "<C>": ["c"]
        }

        checker = RegexConverter(grammar)
        regex = checker.right_linear_grammar_to_regex("<A>")

        self.check_grammar_regex_equivalence(grammar, regex)

    def test_left_linear_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["<B>a", "<A>b", "b"],
            "<B>": ["<C>a", "<B>b"],
            "<C>": ["<A>a", "<C>b"]
        }

        checker = RegexConverter(grammar)
        regex = checker.left_linear_grammar_to_regex("<A>")

        self.check_grammar_regex_equivalence(grammar, regex)

    def test_json_string_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR)
        grammar = converter.grammar_graph.subgraph("<string>").to_grammar()
        regex = converter.right_linear_grammar_to_regex("<string>")

        self.check_grammar_regex_equivalence(grammar, regex)

    def check_grammar_regex_equivalence(self,
                                        grammar: Grammar,
                                        regex: z3.ReRef):
        fuzzer = GrammarCoverageFuzzer(grammar)
        parser = EarleyParser(grammar)

        for _ in range(100):
            inp = fuzzer.fuzz()
            solver = z3.Solver()
            solver.add(z3.InRe(z3.StringVal(inp), regex))
            self.assertEqual(z3.sat, solver.check(), f"Input {inp} not in regex")

        sampler = StringSampler(
            z3.InRe(z3.String("var"), regex),
            grammars={"var": grammar},
            config=StringSamplerConfiguration(reuse_initial_solution=True)
        )

        num_inputs = 0
        for new_assignments in sampler.get_solutions():
            num_inputs += len(new_assignments)
            for new_assignment in new_assignments:
                for _, new_input in new_assignment.items():
                    try:
                        list(parser.parse(new_input))[0]
                    except SyntaxError:
                        self.fail(f"Input {new_input} not in language")

            if num_inputs >= 100:
                break

    @staticmethod
    def smt_check(formula):
        solver = z3.Solver()
        solver.add(formula)
        return solver.check()


if __name__ == '__main__':
    unittest.main()
