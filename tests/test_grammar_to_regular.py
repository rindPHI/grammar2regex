import unittest

from frozendict import frozendict

from grammar_to_regex.grammar_to_regular import (
    analyze_expansions,
    edge_dict_to_set,
    eliminate_recursive_expansion,
    regularize_grammar,
)
from grammar_to_regex.helpers import canonical, compute_closure, edges_in_grammar


class TestGrammarToRegular(unittest.TestCase):
    def test_analyze_expansions_small_artificial(self):
        grammar = canonical(
            {
                "<start>": ["<A>"],  # (ab+)*a
                "<A>": ["a", "a<B><A>"],  # (ab+)*a
                "<B>": ["b", "b<B>"],  # b+
            }
        )

        left_recursive, right_recursive, central_recursive_expansions = map(
            edge_dict_to_set, analyze_expansions(grammar, edges_in_grammar(grammar))
        )

        self.assertFalse(left_recursive)
        self.assertEqual(
            set(right_recursive), {("<A>", (1, 2), "<A>"), ("<B>", (1, 1), "<B>")}
        )
        self.assertFalse(central_recursive_expansions)

    def test_eliminate_expansion_small_artificial(self):
        grammar = canonical(
            {
                "<start>": ["<A>"],  #
                "<A>": ["a", "a<B>"],  # (ab)*a | (ab)+
                "<B>": ["b", "b<A>"],  # b(ab)*
            }
        )

        closure = compute_closure(
            {fr: edges.values() for fr, edges in edges_in_grammar(grammar).items()}
        )

        result = eliminate_recursive_expansion(grammar, closure, "<A>", 1, 1)

        expected = {
            "<start>": (("<A>",),),
            "<A>": (("a",), ("ab",), ("aba",)),
            "<B>": (("b",), ("b", "<A>")),
        }

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

    def test_eliminate_nonregular_recursions_small_artificial(self):
        # In this grammar, no symbol is eliminated: We can compute
        # the language of <B> independently of <A>. What remains
        # is right-linear.
        # TODO: It would not even hurt if <A> was left-linear! Since
        #       <A> and <B> are not in a cycle, they can be regarded
        #       as "independent." We must make this more systematic:
        #       Divide grammars into a *DAG* of sub-grammars; regard
        #       all sub-grammars independently.
        grammar = canonical(
            {
                "<start>": ["<A>"],
                "<A>": ["a", "a<B><A>"],
                "<B>": ["b", "b<B>"],
            }
        )

        result, verdict = regularize_grammar(grammar)

        self.assertEqual("right-linear", verdict)
        self.assertEqual(grammar, result)

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

        result, verdict = regularize_grammar(grammar)

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

        result, verdict = regularize_grammar(grammar)

        # Term stays the same
        self.assertEqual("left-linear", verdict)
        self.assertEqual(grammar["<term>"], result["<term>"])

        # The `(<expression>)` expansion in <factor> is unrolled.
        expected_factor = (
            ("<number>",),
            ("(", "<number>", ")"),
            ("(", "<chars>", ")"),
            ("(", "<number>", " * ", "<number>", ")"),
            ("(", "<number>", " * ", "<chars>", ")"),
            ("(", "<chars>", " * ", "<number>", ")"),
            ("(", "<chars>", " * ", "<chars>", ")"),
            ("(", "<number>", " / ", "<number>", ")"),
            ("(", "<number>", " / ", "<chars>", ")"),
            ("(", "<chars>", " / ", "<number>", ")"),
            ("(", "<chars>", " / ", "<chars>", ")"),
            ("(", "<number>", " + ", "<number>", ")"),
            ("(", "<number>", " + ", "<chars>", ")"),
            ("(", "<chars>", " + ", "<number>", ")"),
            ("(", "<chars>", " + ", "<chars>", ")"),
            ("(", "<number>", " + ", "<number>", " * ", "<number>", ")"),
            ("(", "<number>", " + ", "<number>", " * ", "<chars>", ")"),
            ("(", "<number>", " + ", "<chars>", " * ", "<number>", ")"),
            ("(", "<number>", " + ", "<chars>", " * ", "<chars>", ")"),
            ("(", "<chars>", " + ", "<number>", " * ", "<number>", ")"),
            ("(", "<chars>", " + ", "<number>", " * ", "<chars>", ")"),
            ("(", "<chars>", " + ", "<chars>", " * ", "<number>", ")"),
            ("(", "<chars>", " + ", "<chars>", " * ", "<chars>", ")"),
            ("(", "<number>", " + ", "<number>", " / ", "<number>", ")"),
            ("(", "<number>", " + ", "<number>", " / ", "<chars>", ")"),
            ("(", "<number>", " + ", "<chars>", " / ", "<number>", ")"),
            ("(", "<number>", " + ", "<chars>", " / ", "<chars>", ")"),
            ("(", "<chars>", " + ", "<number>", " / ", "<number>", ")"),
            ("(", "<chars>", " + ", "<number>", " / ", "<chars>", ")"),
            ("(", "<chars>", " + ", "<chars>", " / ", "<number>", ")"),
            ("(", "<chars>", " + ", "<chars>", " / ", "<chars>", ")"),
            ("(", "<number>", " - ", "<number>", ")"),
            ("(", "<number>", " - ", "<chars>", ")"),
            ("(", "<chars>", " - ", "<number>", ")"),
            ("(", "<chars>", " - ", "<chars>", ")"),
            ("(", "<number>", " - ", "<number>", " * ", "<number>", ")"),
            ("(", "<number>", " - ", "<number>", " * ", "<chars>", ")"),
            ("(", "<number>", " - ", "<chars>", " * ", "<number>", ")"),
            ("(", "<number>", " - ", "<chars>", " * ", "<chars>", ")"),
            ("(", "<chars>", " - ", "<number>", " * ", "<number>", ")"),
            ("(", "<chars>", " - ", "<number>", " * ", "<chars>", ")"),
            ("(", "<chars>", " - ", "<chars>", " * ", "<number>", ")"),
            ("(", "<chars>", " - ", "<chars>", " * ", "<chars>", ")"),
            ("(", "<number>", " - ", "<number>", " / ", "<number>", ")"),
            ("(", "<number>", " - ", "<number>", " / ", "<chars>", ")"),
            ("(", "<number>", " - ", "<chars>", " / ", "<number>", ")"),
            ("(", "<number>", " - ", "<chars>", " / ", "<chars>", ")"),
            ("(", "<chars>", " - ", "<number>", " / ", "<number>", ")"),
            ("(", "<chars>", " - ", "<number>", " / ", "<chars>", ")"),
            ("(", "<chars>", " - ", "<chars>", " / ", "<number>", ")"),
            ("(", "<chars>", " - ", "<chars>", " / ", "<chars>", ")"),
            ("<chars>",),
        )

        self.assertEqual(expected_factor, result["<factor>"])


if __name__ == "__main__":
    unittest.main()
