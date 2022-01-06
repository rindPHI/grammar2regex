import copy
import logging
import string
import unittest
from typing import Optional

import pytest
import z3
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Grammars import US_PHONE_GRAMMAR, JSON_GRAMMAR, srange, convert_ebnf_grammar
from fuzzingbook.Parser import EarleyParser
from orderedset import OrderedSet
from string_sampler.sampler import StringSampler, StringSamplerConfiguration, InitialSolutionStrategy

from grammar_to_regex.cfg2regex import RegexConverter, GrammarType, Grammar
from grammar_to_regex.helpers import delete_unreachable
from grammar_to_regex.regex import Concat, Star, Union, Range, Singleton, regex_to_z3
from grammar_to_regex.tests.test_helpers import TestHelpers

# ONLY FOR TESTING, REMOVE FOR DEPLOYMENT
# sys.path.append(path.abspath('../../../StringSMTSampler'))
# END ONLY FOR TESTING, REMOVE FOR DEPLOYMENT

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
        checker = RegexConverter(JSON_GRAMMAR)
        self.assertEqual(
            {('<elements>', 0, 1), ('<array>', 1, 1), ('<object>', 1, 1),
             ('<symbol-1-1>', 1, 1), ('<element>', 0, 1),
             ('<symbol-2>', 1, 1), ('<members>', 0, 1)},
            checker.nonregular_expansions("<elements>"))

    def test_us_phone_grammar_to_regex_from_tree(self):
        checker = RegexConverter(US_PHONE_GRAMMAR)
        regex = regex_to_z3(checker.tree_to_regex("<start>"))

        self.assertEqual(z3.sat, self.smt_check(z3.InRe("(200)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(000)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(200)200-000", regex)))

    def test_us_phone_grammar_to_regex(self):
        logging.basicConfig(level=logging.INFO)
        checker = RegexConverter(US_PHONE_GRAMMAR)
        regex = regex_to_z3(checker.right_linear_grammar_to_regex("<start>"))

        self.check_grammar_regex_inclusion(regex, US_PHONE_GRAMMAR)

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
        self.check_grammar_regex_inclusion(regex_to_z3(regex), grammar, use_string_sampler=False)

    def test_toy_grammar_to_regex(self):
        grammar = RIGHT_LINEAR_TOY_GRAMMAR
        checker = RegexConverter(grammar)
        regex = checker.right_linear_grammar_to_regex("<A>")

        self.check_grammar_regex_inclusion(regex_to_z3(regex), grammar, use_string_sampler=False)

    def test_simple_toy_grammar_to_regex(self):
        grammar = {
            "<start>": ["<A>"],
            "<A>": ["a<B><C>"],
            "<B>": ["b<B>", ""],
            "<C>": ["c"]
        }

        checker = RegexConverter(grammar)
        regex = regex_to_z3(checker.right_linear_grammar_to_regex("<A>"))

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

    def test_json_member_to_regex(self):
        converter = RegexConverter(JSON_GRAMMAR, max_num_expansions=20, compress_unions=True)

        regex = converter.to_regex("<member>", convert_to_z3=False)

        self.check_grammar_regex_inclusion(
            regex_to_z3(regex), JSON_GRAMMAR, allowed_failure_percentage=5, strict=False,
            runs=10,
            string_sampler_config=StringSamplerConfiguration(
                initial_solution_strategy=InitialSolutionStrategy.SMT_PURE,
                max_size_new_neighborhood=200,
            ))

    def test_range_union_equivalence(self):
        logging.basicConfig(level=logging.DEBUG)

        long_union = z3.Plus(
            z3.Union(z3.Re("0"), z3.Re("1"), z3.Re("2"), z3.Re("3"), z3.Re("4"), z3.Re("5"), z3.Re("6"),
                     z3.Re("7"), z3.Re("8"), z3.Re("9"), z3.Re("a"), z3.Re("b"), z3.Re("c"), z3.Re("d"),
                     z3.Re("e"), z3.Re("f"), z3.Re("g"), z3.Re("h"), z3.Re("i"), z3.Re("j"), z3.Re("k"),
                     z3.Re("l"), z3.Re("m"), z3.Re("n"), z3.Re("o"), z3.Re("p"), z3.Re("q"), z3.Re("r"),
                     z3.Re("s"), z3.Re("t"), z3.Re("u"), z3.Re("v"), z3.Re("w"), z3.Re("x"), z3.Re("y"),
                     z3.Re("z"), z3.Re("A"), z3.Re("B"), z3.Re("C"), z3.Re("D"), z3.Re("E"), z3.Re("F"),
                     z3.Re("G"), z3.Re("H"), z3.Re("I"), z3.Re("J"), z3.Re("K"), z3.Re("L"), z3.Re("M"),
                     z3.Re("N"), z3.Re("O"), z3.Re("P"), z3.Re("Q"), z3.Re("R"), z3.Re("S"), z3.Re("T"),
                     z3.Re("U"), z3.Re("V"), z3.Re("W"), z3.Re("X"), z3.Re("Y"), z3.Re("Z"), z3.Re("!"),
                     z3.Re("#"), z3.Re("$"), z3.Re("%"), z3.Re("&"), z3.Re("'"), z3.Re("("), z3.Re(")"),
                     z3.Re("*"), z3.Re("+"), z3.Re(","), z3.Re("-"), z3.Re("."), z3.Re("/"), z3.Re(":"),
                     z3.Re(";"), z3.Re("<"), z3.Re("="), z3.Re(">"), z3.Re("?"), z3.Re("@"), z3.Re("["),
                     z3.Re("]"), z3.Re("^"), z3.Re("_"), z3.Re("`"), z3.Re("{"), z3.Re("|"), z3.Re("}"),
                     z3.Re("~"), z3.Re(" ")))

        short_range_union = z3.Plus(z3.Union(z3.Range(" ", "!"), z3.Range("#", "["), z3.Range("]", "~")))

        grammar = copy.deepcopy(JSON_GRAMMAR)
        grammar["<start>"] = ["<characters>"]
        delete_unreachable(grammar)

        self.check_regex_equivalence(grammar, long_union, short_range_union)

    @pytest.mark.skip(reason="Fails currently in NFA conversion, needs to be fixed.")
    def test_csv_grammar_conversion(self):
        # TODO: This fails currently!!!
        logging.basicConfig(level=logging.DEBUG)

        converter = RegexConverter(CSV_GRAMMAR, max_num_expansions=20, compress_unions=False)
        long_union_regex = converter.to_regex("<raw-string>")
        self.assertTrue(long_union_regex)

    def test_right_linear_id_grammar_conversion(self):
        logging.basicConfig(level=logging.DEBUG)

        grammar = {
            "<start>": ["<id>"],
            "<id>": ["<letter>", "<id><letter>"],
            "<letter>": srange(string.ascii_letters + string.digits + "\"" + "'" + "."),
        }

        converter = RegexConverter(grammar)
        id_regex = converter.to_regex("<id>")

        self.check_grammar_regex_inclusion(
            id_regex, grammar, allowed_failure_percentage=5, strict=False,
            string_sampler_config=StringSamplerConfiguration(
                initial_solution_strategy=InitialSolutionStrategy.SMT_PURE,
                max_size_new_neighborhood=200,
            ))

    def test_range_union_equivalence_csv_fields(self):
        logging.basicConfig(level=logging.DEBUG)

        grammar = copy.deepcopy(CSV_GRAMMAR)
        grammar["<start>"] = ["<raw-field>"]
        delete_unreachable(grammar)

        converter = RegexConverter(grammar, max_num_expansions=20, compress_unions=False)
        long_union_regex = converter.to_regex("<raw-field>")

        converter = RegexConverter(grammar, max_num_expansions=20, compress_unions=True)
        short_range_union = converter.to_regex("<raw-field>")

        self.check_regex_equivalence(grammar, long_union_regex, short_range_union)

    def check_regex_equivalence(self, grammar, re_1, re_2):
        self.logger.debug("Checking inclusion of %s in %s", re_1, re_2)
        self.check_regex_inclusion(grammar, re_1, re_2)
        self.logger.debug("Checking inclusion of %s in %s", re_2, re_1)
        self.check_regex_inclusion(grammar, re_2, re_1)

    def check_regex_inclusion(self, grammar, re_1, re_2):
        # Generate from re_1, check whether this is in re_2
        string_sampler_config = StringSamplerConfiguration(reuse_initial_solution=True)
        sampler = StringSampler(
            z3.InRe(z3.String("var"), re_1),
            z3.BoolVal(True),
            grammars={"var": grammar},
            config=string_sampler_config
        )
        solutions = sampler.get_solutions()
        num_inputs = 0
        while num_inputs < 100:
            try:
                new_assignments = next(solutions)
            except StopIteration:
                break

            num_inputs += len(new_assignments)
            for new_assignment in new_assignments:
                for _, inp in new_assignment.items():
                    # self.logger.debug("Asserting that \"%s\" is in regex %d", inp, i + 1)
                    formula = z3.InRe(z3.StringVal(inp), re_1)
                    solver = z3.Solver()
                    solver.add(formula)
                    # self.assertEqual(z3.sat, solver.check())
                    if solver.check() != z3.sat:
                        continue

                    self.logger.debug("Checking whether \"%s\" is in regex %s", inp, re_2)
                    formula = z3.InRe(z3.StringVal(inp), re_2)
                    solver = z3.Solver()
                    solver.add(formula)

                    self.assertEqual(z3.sat, solver.check())

    def test_json_object_to_regex(self):
        logging.basicConfig(level=logging.DEBUG)
        converter = RegexConverter(JSON_GRAMMAR, max_num_expansions=20)

        regex = converter.to_regex("<start>")

        self.check_grammar_regex_inclusion(
            regex, JSON_GRAMMAR, allowed_failure_percentage=5, strict=False,
            string_sampler_config=StringSamplerConfiguration(
                initial_solution_strategy=InitialSolutionStrategy.SMT_PURE,
                max_size_new_neighborhood=200,
            ))

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

    def test_ranges_xml_id(self):
        xml_id_grammar = {
            "<start>": ["<id>"],
            "<id>": [
                "<id-no-prefix>",
                "<id-with-prefix>"
            ],
            "<id-no-prefix>": [
                "<id-start-char>",
                "<id-start-char><id-chars>",
            ],
            "<id-with-prefix>": ["<id-no-prefix>:<id-no-prefix>"],
            "<id-start-char>": srange("_" + string.ascii_letters),
            "<id-chars>": ["<id-char>", "<id-char><id-chars>"],
            "<id-char>": ["<id-start-char>"] + srange("-." + string.digits),
        }

        converter = RegexConverter(xml_id_grammar, max_num_expansions=20, compress_unions=True)

        regex = converter.to_regex("<id-chars>", convert_to_z3=False)
        self.assertEqual(
            Concat(children=tuple([
                Star(child=Union(children=(
                    Range(from_char='-', to_char='.'),
                    Range(from_char='0', to_char='9'),
                    Range(from_char='A', to_char='Z'),
                    Singleton(child='_'),
                    Range(from_char='a', to_char='z')))),
                Union(children=(
                    Range(from_char='-', to_char='.'),
                    Range(from_char='0', to_char='9'),
                    Range(from_char='A', to_char='Z'),
                    Singleton(child='_'),
                    Range(from_char='a', to_char='z')))])), regex)

        regex = converter.to_regex("<id>")
        self.check_grammar_regex_inclusion(regex, xml_id_grammar)

    def check_grammar_regex_inclusion(
            self,
            regex: z3.ReRef,
            grammar: Grammar,
            runs: int = 100,
            allowed_failure_percentage: int = 0,
            strict: bool = True,
            string_sampler_config: Optional[StringSamplerConfiguration] = None,
            use_string_sampler: bool = True):
        """
        Asserts that regex is, if allowed_failure_percentage is 0, equivalent to grammar, and otherwise a
        strict subset of grammar.
        """
        fuzzer = GrammarCoverageFuzzer(grammar)
        parser = EarleyParser(grammar)

        if not string_sampler_config:
            string_sampler_config = StringSamplerConfiguration(reuse_initial_solution=True)

        # regex \subset grammar
        if use_string_sampler:
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
        else:
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
