import doctest
import unittest

from grammar_to_regex import cfg2regex


class TestDocstrings(unittest.TestCase):
    def test_cfg2regex_new(self):
        doctest_results = doctest.testmod(m=cfg2regex)
        self.assertFalse(doctest_results.failed)


if __name__ == "__main__":
    unittest.main()
