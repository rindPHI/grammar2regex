import unittest

import z3
from fuzzingbook.Grammars import US_PHONE_GRAMMAR, JSON_GRAMMAR

from cfg2regex import RegexConverter, GrammarType


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

    def test_us_phone_grammar_to_regex(self):
        checker = RegexConverter(US_PHONE_GRAMMAR)
        regex = checker.regular_expression_from_tree("<start>")

        self.assertEqual(z3.sat, self.smt_check(z3.InRe("(200)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(000)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(200)200-000", regex)))

    def test_to_dfa(self):
        grammar = {"<start>": ["<A>"],
                   "<A>": ["a<number><B>", "b<A>", "b"],
                   "<B>": ["a<C>", "b<B>"],
                   "<C>": ["a<A>", "b<C>"],
                   "<number>": ["1", "2", "3"]
                   }

        converter = RegexConverter(grammar)
        print(converter.to_dfa("<A>").to_dot())

    @staticmethod
    def smt_check(formula):
        solver = z3.Solver()
        solver.add(formula)
        return solver.check()


if __name__ == '__main__':
    unittest.main()
