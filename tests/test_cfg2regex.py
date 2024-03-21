import copy
import logging
import string
import unittest

import pytest
import z3
from frozendict import frozendict
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import (
    US_PHONE_GRAMMAR,
    JSON_GRAMMAR,
    srange,
    convert_ebnf_grammar,
)
from fuzzingbook.Parser import EarleyParser

from grammar_to_regex.cfg2regex import RegexConverter, Grammar
from grammar_to_regex.helpers import delete_unreachable
from grammar_to_regex.regex import Concat, Star, Singleton, regex_to_z3, concat
from grammar_to_regex.type_defs import FrozenOrderedSet

RIGHT_LINEAR_TOY_GRAMMAR = {
    "<start>": ["<A>"],
    "<A>": ["a<number><B>", "b<A>", "b"],
    "<B>": ["a<C>", "b<B>"],
    "<C>": ["a<A>", "b<C>"],
    "<number>": ["1", "2", "3"],
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
    "<simple-character>": [
        c
        for c in srange(string.printable)
        if c not in ["\n", ";", '"', " ", "\t", "\r"]
    ],
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

    def test_us_phone_grammar_to_regex_from_tree(self):
        checker = RegexConverter(US_PHONE_GRAMMAR)
        regex = checker.to_regex("<start>", convert_to_z3=True)

        self.assertEqual(z3.sat, self.smt_check(z3.InRe("(200)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(000)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(200)200-000", regex)))

    def test_us_phone_grammar_to_regex(self):
        logging.basicConfig(level=logging.INFO)
        checker = RegexConverter(US_PHONE_GRAMMAR, compress_unions=True)
        regex = checker.to_regex("<start>", convert_to_z3=False)
        self.logger.info(regex)

        self.check_grammar_regex_inclusion(regex_to_z3(regex), US_PHONE_GRAMMAR)

    def test_simple_grammar_to_regex(self):
        # a* b
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<A>", "b"],
        }
        checker = RegexConverter(grammar)
        regex = checker.to_regex("<A>", convert_to_z3=False)

        self.assertEqual(
            Concat(children=(Star(child=Singleton(child="a")), Singleton(child="b"))),
            regex,
        )
        self.check_grammar_regex_inclusion(regex_to_z3(regex), grammar, runs=20)

    def test_toy_grammar_to_regex(self):
        grammar = RIGHT_LINEAR_TOY_GRAMMAR
        checker = RegexConverter(grammar)
        regex = checker.to_regex("<A>", convert_to_z3=True)

        self.check_grammar_regex_inclusion(regex, grammar)

    def test_simple_toy_grammar_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><C>"],
            "<B>": ["b<B>", ""],
            "<C>": ["c"],
        }

        checker = RegexConverter(grammar)
        regex = checker.to_regex("<A>", convert_to_z3=True)

        self.check_grammar_regex_inclusion(regex, grammar, runs=30)

    def test_left_linear_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["<B>a", "<A>b", "b"],
            "<B>": ["<C>a", "<B>b"],
            "<C>": ["<A>a", "<C>b"],
        }

        checker = RegexConverter(grammar)
        regex = checker.to_regex("<A>", convert_to_z3=True)

        self.check_grammar_regex_inclusion(regex, grammar)

    def test_json_string_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR)
        regex = converter.to_regex("<string>", convert_to_z3=True)

        grammar = copy.deepcopy(JSON_GRAMMAR)
        grammar["<start>"] = ["<string>"]
        grammar = delete_unreachable(grammar)

        self.check_grammar_regex_inclusion(regex, grammar)

    @pytest.mark.skip
    def test_json_member_to_regex(self):
        converter = RegexConverter(
            JSON_GRAMMAR, max_num_expansions=20, compress_unions=True
        )

        regex = converter.to_regex("<member>", convert_to_z3=False)

        self.check_grammar_regex_inclusion(
            regex_to_z3(regex),
            JSON_GRAMMAR,
            allowed_failure_percentage=5,
            strict=False,
            runs=10,
        )

    # @pytest.mark.skip(reason="Fails currently in NFA conversion, needs to be fixed.")
    def test_csv_grammar_conversion(self):
        logging.basicConfig(level=logging.DEBUG)

        converter = RegexConverter(
            CSV_GRAMMAR, max_num_expansions=3, compress_unions=True
        )
        long_union_regex = converter.to_regex("<raw-string>", convert_to_z3=False)

        grammar = copy.deepcopy(CSV_GRAMMAR)
        grammar["<start>"] = ["<raw-string>"]
        grammar = delete_unreachable(grammar)

        self.check_grammar_regex_inclusion(
            regex_to_z3(long_union_regex),
            grammar,
            allowed_failure_percentage=5,
            strict=False,
        )

    def test_right_linear_id_grammar_conversion(self):
        logging.basicConfig(level=logging.DEBUG)

        grammar = {
            "<start>": ["<id>"],
            "<id>": ["<letter>", "<id><letter>"],
            "<letter>": srange(string.ascii_letters + string.digits + '"' + "'" + "."),
        }

        converter = RegexConverter(grammar)
        id_regex = converter.to_regex("<id>")

        self.check_grammar_regex_inclusion(
            id_regex, grammar, allowed_failure_percentage=5, strict=False
        )

    @pytest.mark.skip
    def test_json_object_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR, max_num_expansions=20)

        regex = converter.to_regex("<start>")

        self.check_grammar_regex_inclusion(
            regex, JSON_GRAMMAR, allowed_failure_percentage=5, strict=False
        )

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
            "<id-char>": ["a"],
        }

        converter = RegexConverter(grammar, max_num_expansions=20, compress_unions=True)

        computed_id_with_prefix_regex = converter.to_regex("<id>", convert_to_z3=False)
        # a*a:a*a
        expected_id_with_prefix_regex = concat(
            Star(Singleton("a")),
            concat(
                concat(Singleton("a"), Singleton(":")),
                Star(Singleton("a")),
                Singleton("a"),
            ),
        )
        self.assertEqual(expected_id_with_prefix_regex, computed_id_with_prefix_regex)

    def test_xml_id(self):
        xml_id_grammar = {
            "<start>": ["<id>"],
            "<id>": ["<id-no-prefix>", "<id-with-prefix>"],
            "<id-no-prefix>": [
                "<id-start-char>",
                "<id-start-char><id-chars>",
            ],
            "<id-with-prefix>": ["<id-no-prefix>:<id-no-prefix>"],
            "<id-start-char>": srange("_" + string.ascii_letters),
            "<id-chars>": ["<id-char>", "<id-char><id-chars>"],
            "<id-char>": ["<id-start-char>"] + srange("-." + string.digits),
        }

        converter = RegexConverter(
            xml_id_grammar, max_num_expansions=3, compress_unions=True
        )
        regex = converter.to_regex("<start>", convert_to_z3=False)

        self.check_grammar_regex_inclusion(
            regex_to_z3(regex),
            xml_id_grammar,
            runs=100,
        )

    def test_arithmetic_expression_grammar(self):
        grammar = {
            "<start>": ["<expression>"],
            "<expression>": [
                "<term>",
                "<expression> + <term>",
                "<expression> - <term>",
            ],
            "<term>": ["<factor>", "<term> * <factor>", "<term> / <factor>"],
            "<factor>": [
                "<number>",
                "(<expression>)",
                "<chars>",
            ],
            # <char><chars> breaks left-linearity.
            "<chars>": ["<char>", "<chars><char>"],
            "<char>": ["a", "b", "c"],
            "<number>": ["<digit>", "<number><digit>"],
            "<digit>": ["0", "1", "2"],
        }

        converter = RegexConverter(grammar, max_num_expansions=3)
        print(converter.to_regex("<start>", convert_to_z3=False))
        # TODO

    def check_grammar_regex_inclusion(
        self,
        regex: z3.ReRef,
        grammar: Grammar,
        runs: int = 100,
        allowed_failure_percentage: int = 0,
        strict: bool = True,
    ):
        """
        Asserts that regex is, if allowed_failure_percentage is 0, equivalent to grammar, and otherwise a
        strict subset of grammar.
        """
        fuzzer = GrammarCoverageFuzzer(grammar)
        parser = EarleyParser(grammar)

        # regex \subset grammar
        prev_solutions: FrozenOrderedSet[str] = frozendict()
        for _ in range(runs):
            s = z3.Solver()
            s.add(z3.InRe(z3.String("var"), regex))
            for p in prev_solutions:
                s.add(z3.Not(z3.String("var") == z3.StringVal(p)))
            assert s.check() == z3.sat

            solution = s.model()[z3.String("var")].as_string()
            try:
                list(parser.parse(solution))[0]
                self.logger.debug(f"Input {solution} is in the grammar")
            except SyntaxError:
                self.fail(f"Input {solution} not in language")
            prev_solutions = prev_solutions.set(solution, None)

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
            self.assertLessEqual(
                fails,
                (allowed_failure_percentage / 100) * runs,
                f"There were {(fails / runs) * 100:0.2f}% failures "
                f"({allowed_failure_percentage}% allowed)",
            )
            if strict:
                self.assertGreater(fails, 0)

    @staticmethod
    def smt_check(formula):
        solver = z3.Solver()
        solver.add(formula)
        return solver.check()


if __name__ == "__main__":
    unittest.main()
