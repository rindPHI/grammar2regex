import unittest

from fuzzingbook.Grammars import US_PHONE_GRAMMAR, JSON_GRAMMAR

from sugrex import RegularityChecker


class TestRegularityChecker(unittest.TestCase):
    def test_us_phone_grammar(self):
        checker = RegularityChecker(US_PHONE_GRAMMAR)
        self.assertTrue(checker.is_regular("<start>"))

    def test_json_grammar(self):
        checker = RegularityChecker(JSON_GRAMMAR)
        self.assertFalse(checker.is_regular("<start>"))

        # <int> would actually be regular, but JSON_GRAMMAR is constructed from a EBNF,
        # which leads to a production <digit><digit-1> for the "+" regex feature, i.e.,
        # there are two nonterminals in the production.
        self.assertFalse(checker.is_regular("<int>"))

    def test_regular_json_int(self):
        pass  # TODO


if __name__ == '__main__':
    unittest.main()
