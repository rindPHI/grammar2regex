import unittest

from frozendict import frozendict

from grammar_to_regex.grammar_to_regular import (
    analyze_expansions,
    edges_in_grammar,
    edge_dict_to_set,
    eliminate_recursive_expansion,
    compute_closure,
    filter_recursive_expansions,
    regularize_grammar,
)
from grammar_to_regex.helpers import canonical


class TestGrammarToRegular(unittest.TestCase):
    def test_analyze_expansions_small_artificial(self):
        grammar = canonical(
            {
                "<start>": ["<A>"],
                "<A>": ["a", "a<B><A>"],
                "<B>": ["b", "b<B>"],
            }
        )

        left_recursive, right_recursive, central_recursive_expansions = map(
            edge_dict_to_set, analyze_expansions(grammar, edges_in_grammar(grammar))
        )

        self.assertFalse(left_recursive)
        self.assertEqual(
            set(right_recursive), {("<A>", (1, 2), "<A>"), ("<B>", (1, 1), "<B>")}
        )
        self.assertEqual(set(central_recursive_expansions), {("<A>", (1, 1), "<B>")})

    def test_eliminate_expansion_small_artificial(self):
        grammar = canonical(
            {
                "<start>": ["<A>"],
                "<A>": ["a", "a<B><A>"],
                "<B>": ["b", "b<B>"],
            }
        )

        closure = compute_closure(
            {fr: edges.values() for fr, edges in edges_in_grammar(grammar).items()}
        )

        result = eliminate_recursive_expansion(grammar, closure, "<A>", 1, 1)

        expected = canonical(
            {
                "<start>": ("<A>",),
                "<A>": ("a", "ab<A>", "abb<A>", "abbb<A>"),
                "<B>": ("b", "b<B>"),
            }
        )

        self.assertEqual(dict(expected), dict(result))

    def test_eliminate_recursive_expansion_chars(self):
        grammar = canonical(
            {
                "<start>": ["<chars>"],
                "<chars>": ["<char>", "<char><chars>"],
            }
        )

        closure = compute_closure(
            {fr: edges.values() for fr, edges in edges_in_grammar(grammar).items()}
        )

        result = eliminate_recursive_expansion(grammar, closure, "<chars>", 1, 1)

        expected = frozendict(
            {
                "<start>": (("<chars>",),),
                "<chars>": (
                    ("<char>",),
                    ("<char>", "<char>"),
                ),
            }
        )

        self.assertEqual(expected, result)

    def test_filter_recursive_expansions_small_artificial(self):
        grammar = canonical(
            {
                "<start>": ["<A>"],
                "<A>": ["a", "a<B><A>"],
                "<B>": ["b", "b<B>"],
            }
        )

        closure = compute_closure(
            {fr: edges.values() for fr, edges in edges_in_grammar(grammar).items()}
        )

        expansions = (
            ("a",),
            ("ab", "<A>"),
            ("abb", "<A>"),
            ("abbb", "<A>"),
            ("abbbb", "<A>"),
            ("abbbb", "<B>", "<A>"),
        )

        expected = (
            ("a",),
            ("ab", "<A>"),
            ("abb", "<A>"),
            ("abbb", "<A>"),
            ("abbbb", "<A>"),
        )

        self.assertEqual(
            expected,
            filter_recursive_expansions(
                expansions, "<A>", closure, allow_short_circuits=True
            ),
        )

    def test_eliminate_nonregular_recursions_small_artificial(self):
        grammar = canonical(
            {
                "<start>": ["<A>"],
                "<A>": ["a", "a<B><A>"],
                "<B>": ["b", "b<B>"],
            }
        )

        expected = frozendict(
            {
                "<start>": (("<A>",),),
                "<A>": (("a",), ("ab", "<A>"), ("abb", "<A>"), ("abbb", "<A>")),
                "<B>": (("b",), ("b", "<B>")),
            }
        )

        result, verdict = regularize_grammar(grammar)

        self.assertEqual("right-linear", verdict)
        self.assertEqual(expected, result)

    def test_regularize_grammar_small_artificial_extended(self):
        grammar = canonical(
            {
                "<start>": ["<A>"],
                "<A>": ["a", "a<B><A>"],
                "<B>": ["b", "b<C><B>"],
                "<C>": ["c"],
            }
        )

        expected = frozendict(
            {
                "<A>": (("a",), ("ab", "<A>"), ("abcb", "<A>"), ("abcbcb", "<A>")),
                "<B>": (("b",), ("bc", "<B>")),
                "<C>": (("c",),),
                "<start>": (("<A>",),),
            }
        )

        result, verdict = regularize_grammar(
            grammar, inline_nonrecursive_nonterminals=True
        )

        self.assertEqual("right-linear", verdict)
        self.assertEqual(dict(expected), dict(result))

    def test_even_left_and_right_recursive_symbols(self):
        grammar = canonical(
            {
                "<start>": ["<expression>"],
                "<expression>": [
                    "<chars>",
                    "<number>",
                ],
                # Right recursion wins in case of a tie: The <chars>
                # alternatives remain unchanged.
                "<chars>": ["<char>", "<char><chars>"],
                "<char>": ["a", "b", "c"],
                # The <number> alternatives are inlined.
                "<number>": ["<digit>", "<number><digit>"],
                "<digit>": ["0", "1", "2"],
            }
        )

        result, verdict = regularize_grammar(
            grammar, inline_nonrecursive_nonterminals=False
        )

        expected = canonical(
            {
                "<start>": ["<expression>"],
                "<expression>": [
                    "<chars>",
                    "<number>",
                ],
                "<chars>": ["<char>", "<char><chars>"],
                "<char>": ["a", "b", "c"],
                "<number>": ["<digit>", "<digit><digit>"],
                "<digit>": ["0", "1", "2"],
            }
        )

        self.assertEqual("right-linear", verdict)
        self.assertEqual(expected, result)

    def test_regularize_arithmetic_expression_grammar(self):
        grammar = canonical(
            {
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
                "<char>": ["a", "b", "c", "$", "_"],
                "<number>": ["<digit>", "<number><digit>"],
                "<digit>": ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"],
            }
        )

        result, verdict = regularize_grammar(
            grammar, inline_nonrecursive_nonterminals=False
        )

        expected_term = (
            ("<factor>",),
            ("<term>", " * ", "<digit>"),
            ("<term>", " * ", "<digit>", "<digit>"),
            ("<term>", " * (", "<digit>", ")"),
            ("<term>", " * (", "<digit>", "<digit>", ")"),
            ("<term>", " * (", "<digit>", "<digit>", "<digit>", ")"),
            ("<term>", " * (", "<char>", ")"),
            ("<term>", " * (", "<char>", "<char>", ")"),
            ("<term>", " * (", "<char>", "<char>", "<char>", ")"),
            ("<term>", " * ", "<char>"),
            ("<term>", " * ", "<char>", "<char>"),
            ("<term>", " / ", "<digit>"),
            ("<term>", " / ", "<digit>", "<digit>"),
            ("<term>", " / (", "<digit>", ")"),
            ("<term>", " / (", "<digit>", "<digit>", ")"),
            ("<term>", " / (", "<digit>", "<digit>", "<digit>", ")"),
            ("<term>", " / (", "<char>", ")"),
            ("<term>", " / (", "<char>", "<char>", ")"),
            ("<term>", " / (", "<char>", "<char>", "<char>", ")"),
            ("<term>", " / ", "<char>"),
            ("<term>", " / ", "<char>", "<char>"),
        )

        self.assertEqual("left-linear", verdict)
        self.assertEqual(expected_term, result["<term>"])


if __name__ == "__main__":
    unittest.main()
