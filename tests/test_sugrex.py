import unittest

import z3
from fuzzingbook.Grammars import US_PHONE_GRAMMAR, JSON_GRAMMAR

from sugrex import RegularityChecker


class TestRegularityChecker(unittest.TestCase):
    def test_us_phone_grammar_regularity(self):
        checker = RegularityChecker(US_PHONE_GRAMMAR)
        self.assertTrue(checker.is_regular("<start>"))

    def test_json_grammar_regularity(self):
        checker = RegularityChecker(JSON_GRAMMAR)
        self.assertFalse(checker.is_regular("<start>"))
        self.assertFalse(checker.is_regular("<value>"))

        self.assertTrue(checker.is_regular("<int>"))
        self.assertTrue(checker.is_regular("<string>"))

    def test_us_phone_grammar_to_regex(self):
        checker = RegularityChecker(US_PHONE_GRAMMAR)
        regex = checker.regular_expression_from_tree("<start>")

        self.assertEqual(z3.sat, self.smt_check(z3.InRe("(200)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(000)200-0000", regex)))
        self.assertEqual(z3.unsat, self.smt_check(z3.InRe("(200)200-000", regex)))

    @staticmethod
    def smt_check(formula):
        solver = z3.Solver()
        solver.add(formula)
        return solver.check()


if __name__ == '__main__':
    unittest.main()
