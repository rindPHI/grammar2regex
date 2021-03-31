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
        self.assertFalse(checker.is_regular("<value>"))

        self.assertTrue(checker.is_regular("<int>"))
        self.assertTrue(checker.is_regular("<string>"))


if __name__ == '__main__':
    unittest.main()
