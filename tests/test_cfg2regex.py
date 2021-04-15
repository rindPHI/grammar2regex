import logging
import unittest
from typing import List

import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import US_PHONE_GRAMMAR, JSON_GRAMMAR
from fuzzingbook.Parser import EarleyParser, State
from string_sampler import StringSampler, FastFeedbackParser

from cfg2regex import RegexConverter, GrammarType
from nfa import NFA

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
        regex = checker.regular_expression_from_tree("<start>")

        self.assertEqual(z3.sat, self.smt_check(z3.InRe("(200)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(000)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(200)200-000", regex)))

    def test_us_phone_grammar_to_regex(self):
        checker = RegexConverter(US_PHONE_GRAMMAR)
        regex = checker.to_regex("<start>")

        fuzzer = GrammarCoverageFuzzer(US_PHONE_GRAMMAR)
        parser = fast_feedback_parser(EarleyParser(US_PHONE_GRAMMAR))

        self.check_grammar_regex_equivalence(fuzzer, parser, regex)

    def test_toy_grammar_to_nfa(self):
        checker = RegexConverter(RIGHT_LINEAR_TOY_GRAMMAR)
        checker.to_nfa("<A>")
        # No Exception

    def test_toy_grammar_to_regex(self):
        checker = RegexConverter(RIGHT_LINEAR_TOY_GRAMMAR)
        grammar = checker.grammar_graph.subgraph("<A>").to_grammar()
        regex = checker.to_regex("<A>")

        fuzzer = GrammarCoverageFuzzer(grammar)
        parser = fast_feedback_parser(EarleyParser(grammar))

        self.check_grammar_regex_equivalence(fuzzer, parser, regex)

    def test_simple_toy_grammar_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><C>"],
            "<B>": ["b<B>", ""],
            "<C>": ["c"]
        }

        checker = RegexConverter(grammar)
        regex = checker.to_regex("<A>")

        fuzzer = GrammarCoverageFuzzer(grammar)
        parser = fast_feedback_parser(EarleyParser(grammar))

        self.check_grammar_regex_equivalence(fuzzer, parser, regex)

    def test_to_dfa_json(self):
        converter = RegexConverter(JSON_GRAMMAR)
        print(converter.to_nfa("<string>").to_dot())

    def check_grammar_regex_equivalence(self,
                                        fuzzer: GrammarCoverageFuzzer,
                                        parser: FastFeedbackParser,
                                        regex: z3.ReRef):
        for _ in range(100):
            inp = fuzzer.fuzz()
            solver = z3.Solver()
            solver.add(z3.InRe(z3.StringVal(inp), regex))
            self.assertEqual(z3.sat, solver.check(), f"Input {inp} not in regex")

        sampler = StringSampler(
            z3.InRe(z3.String("var"), regex),
            generators={"var": lambda: fuzzer.fuzz()},
            parsers={"var": parser}
        )

        num_inputs = 0
        for new_assignments in sampler.get_solutions():
            if num_inputs >= 100:
                break

            num_inputs += len(new_assignments)
            for new_assignment in new_assignments:
                for _, new_input in new_assignment.items():
                    self.assertEqual(FastFeedbackParser.Feedback.VALID, parser(new_input),
                                     f"Input {new_input} not in language")

    @staticmethod
    def smt_check(formula):
        solver = z3.Solver()
        solver.add(formula)
        return solver.check()


def fast_feedback_parser(parser: EarleyParser) -> FastFeedbackParser:
    def run(inp: str) -> FastFeedbackParser.Feedback:
        states: List[State] = parser.chart_parse(inp, parser.start_symbol())[-1].states

        if not states:
            return FastFeedbackParser.Feedback.INVALID
        elif states[-1].finished():
            return FastFeedbackParser.Feedback.VALID
        else:
            return FastFeedbackParser.Feedback.INCOMPLETE

    result = FastFeedbackParser()
    result.run = run
    return result


if __name__ == '__main__':
    unittest.main()
