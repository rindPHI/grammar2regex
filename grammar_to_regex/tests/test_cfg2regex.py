import logging
import unittest
from os import path
from typing import Union

import sys
import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import US_PHONE_GRAMMAR, JSON_GRAMMAR
from fuzzingbook.Parser import EarleyParser
from orderedset import OrderedSet

from grammar_to_regex.cfg2regex import RegexConverter, GrammarType, Grammar
from grammar_to_regex.tests.test_helpers import TestHelpers

# ONLY FOR TESTING, REMOVE FOR DEPLOYMENT
sys.path.append(path.abspath('../../../StringSMTSampler'))
# END ONLY FOR TESTING, REMOVE FOR DEPLOYMENT

from string_sampler.sampler import StringSampler, StringSamplerConfiguration, InitialSolutionStrategy

RIGHT_LINEAR_TOY_GRAMMAR = \
    {"<start>": ["<A>"],
     "<A>": ["a<number><B>", "b<A>", "b"],
     "<B>": ["a<C>", "b<B>"],
     "<C>": ["a<A>", "b<C>"],
     "<number>": ["1", "2", "3"]
     }


class TestRegexConverter(unittest.TestCase):
    def __init__(self, *args):
        super().__init__(*args)
        self.logger = logging.getLogger(type(self).__name__)

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

    def test_json_grammar_nonregular_expansions(self):
        checker = RegexConverter(JSON_GRAMMAR)
        self.assertEqual(
            {('<elements>', 0, 1), ('<array>', 1, 1), ('<object>', 1, 1),
             ('<symbol-1-1>', 1, 1), ('<element>', 0, 1),
             ('<symbol-2>', 1, 1), ('<members>', 0, 1)},
            checker.nonregular_expansions("<elements>"))

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

        self.check_grammar_regex_inclusion(regex, US_PHONE_GRAMMAR)

    def test_toy_grammar_to_nfa(self):
        checker = RegexConverter(RIGHT_LINEAR_TOY_GRAMMAR)
        checker.right_linear_grammar_to_nfa("<A>")
        # No Exception

    def test_toy_grammar_to_regex(self):
        checker = RegexConverter(RIGHT_LINEAR_TOY_GRAMMAR)
        regex = checker.right_linear_grammar_to_regex("<A>")

        self.check_grammar_regex_inclusion(regex, RIGHT_LINEAR_TOY_GRAMMAR)

    def test_simple_toy_grammar_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><C>"],
            "<B>": ["b<B>", ""],
            "<C>": ["c"]
        }

        checker = RegexConverter(grammar)
        regex = checker.right_linear_grammar_to_regex("<A>")

        self.check_grammar_regex_inclusion(regex, grammar)

    def test_left_linear_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["<B>a", "<A>b", "b"],
            "<B>": ["<C>a", "<B>b"],
            "<C>": ["<A>a", "<C>b"]
        }

        checker = RegexConverter(grammar)
        regex = checker.left_linear_grammar_to_regex("<A>")

        self.check_grammar_regex_inclusion(regex, grammar)

    def test_json_string_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR)
        grammar = converter.grammar_graph.subgraph("<string>").to_grammar()
        regex = converter.right_linear_grammar_to_regex("<string>")

        self.check_grammar_regex_inclusion(regex, grammar)

    # TODO: Grammar conversion of <member> does not work...
    def test_json_member_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR, max_num_expansions=20)

        regex = converter.to_regex("<member>")

        self.check_grammar_regex_inclusion(regex, JSON_GRAMMAR, allowed_failure_percentage=5, strict=False,
                                           string_sampler_config=StringSamplerConfiguration(
                                               initial_solution_strategy=InitialSolutionStrategy.SMT_PURE,
                                               max_size_new_neighborhood=200,
                                           ))

    def test_json_object_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR, max_num_expansions=20)

        regex = converter.to_regex("<start>")

        self.check_grammar_regex_inclusion(regex, JSON_GRAMMAR, allowed_failure_percentage=5, strict=False,
                                           string_sampler_config=StringSamplerConfiguration(
                                               initial_solution_strategy=InitialSolutionStrategy.SMT_PURE,
                                               max_size_new_neighborhood=200,
                                           ))

    def test_json_constraint(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR, max_num_expansions=20)
        # Forall $member: <member> in <start>,
        #   Forall $string left of ":" in $member,
        #     $string == '"key"'

        v_start = z3.String("$start")
        v_member = z3.String("$member")
        v_string = z3.String("$string")

        # json_regex = converter.to_regex("<start>")
        # member_regex = converter.to_regex("<member>")
        string_regex = converter.to_regex("<string>")

        ###
        test_for = z3.Exists([v_string],
                             z3.And(
                                 # z3.InRe(v_member, member_regex),
                                 z3.InRe(v_string, string_regex),
                                 z3.Contains(v_member, v_string),
                                 v_string == z3.StringVal('"key"')))
        solver = z3.Solver()
        solver.add(test_for)
        print(solver.check())
        print(solver.model())
        return
        ###

        formula_with_re = z3.ForAll([v_member, v_string],
                                    z3.Implies(
                                        z3.And(
                                            z3.InRe(v_start, json_regex),
                                            z3.InRe(v_member, member_regex),
                                            z3.InRe(v_string, string_regex),
                                            z3.Contains(v_start, v_member),
                                            z3.Contains(v_member, v_string),
                                            z3.IndexOf(v_member, v_string) < z3.IndexOf(v_member, z3.StringVal(":"))
                                        ),
                                        v_string == z3.StringVal('"key"')
                                    ))
        solver = z3.Solver()
        solver.add(formula_with_re)
        print(solver.check())

    def test_unwind_expansion(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><B><C>"],
            "<B>": ["<B>b", "<C><B>", ""],
            "<C>": ["c"]
        }

        checker = RegexConverter(grammar, max_num_expansions=10)
        unwound_grammar = checker.unwind_grammar(OrderedSet([("<A>", 0, 2), ("<A>", 0, 1)]))
        TestHelpers.assert_grammar_inclusion(self, unwound_grammar, grammar, allowed_failure_percentage=5)

    def check_grammar_regex_inclusion(self,
                                      regex: z3.ReRef,
                                      grammar: Grammar,
                                      runs: int = 100,
                                      allowed_failure_percentage: int = 0,
                                      strict: bool = True,
                                      string_sampler_config: Union[None, StringSamplerConfiguration] = None):
        """
        Asserts that regex is, if allowed_failure_percentage is 0, equivalent to grammar, and otherwise a
        strict subset of grammar.
        """
        fuzzer = GrammarCoverageFuzzer(grammar)
        parser = EarleyParser(grammar)

        if not string_sampler_config:
            string_sampler_config = StringSamplerConfiguration(reuse_initial_solution=True)

        # regex \subset grammar
        sampler = StringSampler(
            z3.InRe(z3.String("var"), regex),
            z3.BoolVal(True),
            grammars={"var": grammar},
            config=string_sampler_config
        )

        num_inputs = 0
        for new_assignments in sampler.get_solutions():
            num_inputs += len(new_assignments)
            self.logger.debug(f"Generated {num_inputs} instantiations")
            for new_assignment in new_assignments:
                for _, new_input in new_assignment.items():
                    try:
                        list(parser.parse(new_input))[0]
                    except SyntaxError:
                        self.fail(f"Input {new_input} not in language")

            if num_inputs >= runs:
                break

        # grammar \subset regex

        # Evaluator caches compiled regular expressions, have to reuse for performance!
        # For this example, actually, using z3 is *much* quicker...
        # evaluator = ConstraintEvaluator()

        fails = 0
        for _ in range(runs):
            inp = fuzzer.fuzz()
            formula = z3.InRe(z3.StringVal(inp), regex)
            self.logger.debug(f"Checking whether {inp} is in regex")

            # result = evaluator.eval(formula)

            solver = z3.Solver()
            solver.add(formula)
            result = solver.check() == z3.sat

            if not result:
                self.logger.debug(f"Input {inp} not in regular expression")
                if allowed_failure_percentage == 0:
                    self.assertEqual(True, result, f"Input {inp} not in regex")
                else:
                    fails += 1

            self.logger.debug(f"Input {inp} is in regular expression")

        if allowed_failure_percentage > 0:
            self.assertLessEqual(fails, (allowed_failure_percentage / 100) * runs,
                                 f"There were {(fails / runs) * 100:0.2f}% failures "
                                 f"({allowed_failure_percentage}% allowed)")
            if strict:
                self.assertGreater(fails, 0)

    @staticmethod
    def smt_check(formula):
        solver = z3.Solver()
        solver.add(formula)
        return solver.check()


if __name__ == '__main__':
    unittest.main()
