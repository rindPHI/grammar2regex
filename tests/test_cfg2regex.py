import copy
import json
import logging
import string
import unittest

import pytest
import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import US_PHONE_GRAMMAR, JSON_GRAMMAR, srange, convert_ebnf_grammar
from fuzzingbook.Parser import EarleyParser
from orderedset import OrderedSet

from grammar_to_regex.cfg2regex import RegexConverter, GrammarType, Grammar
from grammar_to_regex.helpers import delete_unreachable
from grammar_to_regex.regex import Concat, Star, Singleton, regex_to_z3, concat
from grep_grammar import REDUCED_GREP_GRAMMAR, GREP_GRAMMAR
from tests.test_helpers import TestHelpers

RIGHT_LINEAR_TOY_GRAMMAR = \
    {"<start>": ["<A>"],
     "<A>": ["a<number><B>", "b<A>", "b"],
     "<B>": ["a<C>", "b<B>"],
     "<C>": ["a<A>", "b<C>"],
     "<number>": ["1", "2", "3"]
     }

CSV_EBNF_GRAMMAR = {
    "<start>": ["<csv-file>"],
    "<csv-file>": ["<csv-header><csv-record>*"],
    "<csv-header>": ["<csv-record>"],
    "<csv-record>": ["<csv-string-list>\n"],
    "<csv-string-list>": ["<raw-string>", "<raw-string>;<csv-string-list>"],
    "<raw-string>": ["<spaces>", "<spaces>?<raw-field><spaces>?"],
    "<raw-field>": ["<simple-field>", "<quoted-field>"],
    "<simple-field>": ["<simple-character>*"],
    "<simple-character>": [c for c in srange(string.printable) if c not in ["\n", ";", '"', " ", "\t", "\r"]],
    "<quoted-field>": ['"<escaped-field>"'],
    "<escaped-field>": ["<escaped-character>*"],
    "<escaped-character>": [c for c in srange(string.printable) if c not in ['"']],
    "<spaces>": [" ", " <spaces>"],
}

CSV_GRAMMAR = convert_ebnf_grammar(CSV_EBNF_GRAMMAR)


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
        # TODO: Validate this example manually!

        checker = RegexConverter(JSON_GRAMMAR)
        expansions = checker.nonregular_expansions("<elements>")
        self.logger.info(checker.grammar_type)
        self.assertEqual(
            {('<array>', 1, 1),
             ('<character-1>', 1, 1),
             ('<digit-1>', 1, 1),
             ('<element>', 0, 1),
             ('<elements>', 0, 1),
             ('<member>', 0, 4),
             ('<members>', 0, 1),
             ('<object>', 1, 1),
             ('<symbol-1-1>', 1, 1),
             ('<symbol-1>', 0, 1),
             ('<symbol-2>', 1, 1),
             ('<symbol>', 0, 1)},
            set(expansions))

    def test_us_phone_grammar_to_regex_from_tree(self):
        checker = RegexConverter(US_PHONE_GRAMMAR)
        regex = regex_to_z3(checker.tree_to_regex("<start>"))

        self.assertEqual(z3.sat, self.smt_check(z3.InRe("(200)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(000)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(200)200-000", regex)))

    def test_us_phone_grammar_to_regex(self):
        logging.basicConfig(level=logging.INFO)
        checker = RegexConverter(US_PHONE_GRAMMAR, compress_unions=True)
        regex = checker.to_regex("<start>", convert_to_z3=False)
        self.logger.info(regex)

        self.check_grammar_regex_inclusion(regex_to_z3(regex), US_PHONE_GRAMMAR)

    def test_toy_grammar_to_nfa(self):
        checker = RegexConverter(RIGHT_LINEAR_TOY_GRAMMAR)
        checker.right_linear_grammar_to_nfa("<A>")
        # No Exception

    def test_simple_grammar_to_regex(self):
        # a* b
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<A>", "b"],
        }
        checker = RegexConverter(grammar)
        regex = checker.right_linear_grammar_to_regex("<A>")

        self.assertEqual(Concat(children=(Star(child=Singleton(child='a')), Singleton(child='b'))), regex)
        self.check_grammar_regex_inclusion(regex_to_z3(regex), grammar)

    def test_toy_grammar_to_regex(self):
        grammar = RIGHT_LINEAR_TOY_GRAMMAR
        checker = RegexConverter(grammar)
        regex = checker.right_linear_grammar_to_regex("<A>")

        self.check_grammar_regex_inclusion(regex_to_z3(regex), grammar)

    def test_simple_toy_grammar_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><C>"],
            "<B>": ["b<B>", ""],
            "<C>": ["c"]
        }

        checker = RegexConverter(grammar)
        regex = regex_to_z3(checker.right_linear_grammar_to_regex("<A>"))
        self.logger.info(regex)

        self.check_grammar_regex_inclusion(regex, grammar)

    def test_left_linear_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["<B>a", "<A>b", "b"],
            "<B>": ["<C>a", "<B>b"],
            "<C>": ["<A>a", "<C>b"]
        }

        checker = RegexConverter(grammar)
        regex = regex_to_z3(checker.left_linear_grammar_to_regex("<A>"))

        self.check_grammar_regex_inclusion(regex, grammar)

    def test_json_string_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR)
        grammar = converter.grammar_graph.subgraph("<string>").to_grammar()
        regex = regex_to_z3(converter.right_linear_grammar_to_regex("<string>"))

        self.check_grammar_regex_inclusion(regex, grammar)

    @pytest.mark.skip
    def test_json_member_to_regex(self):
        converter = RegexConverter(JSON_GRAMMAR, max_num_expansions=20, compress_unions=True)

        regex = converter.to_regex("<member>", convert_to_z3=False)

        self.check_grammar_regex_inclusion(
            regex_to_z3(regex), JSON_GRAMMAR, allowed_failure_percentage=5, strict=False,
            runs=10)

    # @pytest.mark.skip(reason="Fails currently in NFA conversion, needs to be fixed.")
    def test_csv_grammar_conversion(self):
        logging.basicConfig(level=logging.DEBUG)

        converter = RegexConverter(CSV_GRAMMAR, max_num_expansions=20, compress_unions=True)
        long_union_regex = converter.to_regex("<raw-string>", convert_to_z3=False)

        grammar = copy.deepcopy(CSV_GRAMMAR)
        grammar["<start>"] = ["<raw-string>"]
        delete_unreachable(grammar)

        self.check_grammar_regex_inclusion(
            regex_to_z3(long_union_regex), grammar, allowed_failure_percentage=5, strict=False)

    def test_right_linear_id_grammar_conversion(self):
        logging.basicConfig(level=logging.DEBUG)

        grammar = {
            "<start>": ["<id>"],
            "<id>": ["<letter>", "<id><letter>"],
            "<letter>": srange(string.ascii_letters + string.digits + "\"" + "'" + "."),
        }

        converter = RegexConverter(grammar)
        id_regex = converter.to_regex("<id>")

        self.check_grammar_regex_inclusion(id_regex, grammar, allowed_failure_percentage=5, strict=False)

    @pytest.mark.skip
    def test_json_object_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR, max_num_expansions=20)

        regex = converter.to_regex("<start>")

        self.check_grammar_regex_inclusion(regex, JSON_GRAMMAR, allowed_failure_percentage=5, strict=False)

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

    def test_ranges(self):
        grammar = {
            "<start>": ["<nobr-char>"],
            "<nobr-char>": list(set(srange(string.printable)) - {"\n", "\r"}),
        }

        converter = RegexConverter(grammar, max_num_expansions=20, compress_unions=True)
        regex = converter.to_regex("<start>")

        solver = z3.Solver()
        solver.add(z3.InRe(z3.StringVal("?"), regex))
        self.assertEqual(z3.sat, solver.check())

        solver = z3.Solver()
        solver.add(z3.InRe(z3.StringVal("\n"), regex))
        self.assertEqual(z3.unsat, solver.check())

    def test_xml_id_simplified(self):
        grammar = {
            "<start>": ["<id>"],
            "<id>": ["<id-chars>:<id-chars>"],
            "<id-chars>": ["<id-char>", "<id-char><id-chars>"],
            "<id-char>": ["a"]
        }

        converter = RegexConverter(grammar, max_num_expansions=20, compress_unions=True)

        computed_id_with_prefix_regex = converter.to_regex("<id>", convert_to_z3=False)
        # a*a:a*a
        expected_id_with_prefix_regex = concat(
            Star(Singleton('a')),
            concat(
                concat(Singleton('a'), Singleton(':')),
                Star(Singleton('a')),
                Singleton('a')))
        self.assertEqual(expected_id_with_prefix_regex, computed_id_with_prefix_regex)

    def test_unwind_mutually_recursive_grammar(self):
        grammar = {
            '<start>': ['<A>'],
            '<A>': [
                '',
                '<A><B>'
            ],
            '<B>': [
                '<As>',
                '<A>'
            ],
            '<As>': ['a', 'a<As>'],
        }

        checker = RegexConverter(grammar, max_num_expansions=3)

        problematic_expansions = checker.nonregular_expansions('<start>')
        self.logger.info('Problematic expansions:\n%s', problematic_expansions)

        unwound_grammar = checker.unwind_grammar(problematic_expansions)
        unwound_checker = RegexConverter(unwound_grammar)

        self.assertFalse(unwound_checker.nonregular_expansions('<start>'))
        self.assertTrue(unwound_checker.is_regular('<start>'))

    def test_unwind_grep_grammar(self):
        pattern_grammar = copy.deepcopy(GREP_GRAMMAR)
        pattern_grammar['<start>'] = ['<pattern>']
        delete_unreachable(pattern_grammar)

        checker = RegexConverter(pattern_grammar, max_num_expansions=3)

        problematic_expansions = checker.nonregular_expansions('<start>')
        self.assertEqual(GrammarType.RIGHT_LINEAR, checker.grammar_type)
        self.assertEqual(
            {('<expression>', 3, 0), ('<expression>', 4, 0), ('<expression>', 5, 1), ('<regex>', 1, 0)},
            problematic_expansions)

        unwound_grammar = checker.unwind_grammar(problematic_expansions)
        unwound_checker = RegexConverter(unwound_grammar)

        self.assertFalse(unwound_checker.nonregular_expansions('<start>'))
        self.assertTrue(unwound_checker.is_regular('<start>'))

    def test_unwind_grammar(self):
        grammar = {'<start>': ['<A>'], '<A>': ['', '<A><As>', '<A>'], '<As>': ['a', 'a<As>']}
        checker = RegexConverter(grammar, max_num_expansions=3)
        problematic_expansions = checker.nonregular_expansions('<start>')
        self.assertEqual({('<As>', 1, 1)}, problematic_expansions)
        self.assertEqual(
            {'<start>': ['<A>'], '<A>': ['', '<A><As>', '<A>'], '<As>': ['a', 'aa', 'aaa']},
            checker.unwind_grammar(problematic_expansions))

    def check_grammar_regex_inclusion(
            self,
            regex: z3.ReRef,
            grammar: Grammar,
            runs: int = 100,
            allowed_failure_percentage: int = 0,
            strict: bool = True):
        """
        Asserts that regex is, if allowed_failure_percentage is 0, equivalent to grammar, and otherwise a
        strict subset of grammar.
        """
        fuzzer = GrammarCoverageFuzzer(grammar)
        parser = EarleyParser(grammar)

        # regex \subset grammar
        prev_solutions: OrderedSet[str] = OrderedSet()
        for _ in range(runs):
            s = z3.Solver()
            s.add(z3.InRe(z3.String("var"), regex))
            for p in prev_solutions:
                s.add(z3.Not(z3.String("var") == z3.StringVal(p)))
            assert s.check() == z3.sat

            solution = s.model()[z3.String("var")].as_string()
            try:
                list(parser.parse(solution))[0]
            except SyntaxError:
                self.fail(f"Input {solution} not in language")
            prev_solutions.add(solution)

        # grammar \subset regex

        # Evaluator caches compiled regular expressions, have to reuse for performance!
        # For this example, actually, using z3 is *much* quicker...
        # evaluator = ConstraintEvaluator()

        fails = 0
        for _ in range(runs):
            inp = fuzzer.fuzz()
            formula = z3.InRe(z3.StringVal(inp), regex)
            # result = evaluator.eval(formula)

            solver = z3.Solver()
            solver.add(formula)
            result = solver.check() == z3.sat

            if not result:
                self.logger.debug(f"Input {inp} not in regex")
                if allowed_failure_percentage == 0:
                    self.assertEqual(True, result, f"Input {inp} not in regex")
                else:
                    fails += 1
            else:
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
