import itertools
import logging
from functools import cache
from typing import Tuple, Optional, TypeAlias

import z3
from frozendict import frozendict

from grammar_to_regex.grammar_to_regular import (
    regularize_grammar,
    LEFT_LINEAR,
    RIGHT_LINEAR,
    NON_RECURSIVE,
)
from grammar_to_regex.helpers import (
    canonical,
    compute_closure,
    edges_in_grammar,
)
from grammar_to_regex.helpers import (
    is_nonterminal,
    fresh_nonterminal,
    consecutive_numbers,
)
from grammar_to_regex.regex import (
    Regex,
    Singleton,
    Star,
    Union,
    Concat,
    Range,
    union,
    concat,
    epsilon,
    star,
)
from grammar_to_regex.regex import (
    regex_to_z3,
)
from grammar_to_regex.type_defs import (
    CanonicalGrammar,
    FrozenCanonicalGrammar,
    FrozenOrderedSet,
)
from grammar_to_regex.type_defs import Grammar

LOGGER = logging.getLogger(__name__)

IntermediateGrammar: TypeAlias = frozendict[str, Tuple[Tuple[Regex, str] | Regex, ...]]


class RegexConverter:
    def __init__(
        self,
        grammar: Grammar,
        max_num_expansions: int = 3,
        expansion_depth_direct_recursion: int = 1,
        compress_unions: bool = False,
    ):
        """
        *LEGACY INTERFACE*

        :param grammar: The underlying grammar.
        :param max_num_expansions: For non-regular (sub) grammars,
            we can unwind problematic nonterminals in expansions.
            This parameter sets a depth bound on the number of unwindings.
        :param expansion_depth_direct_recursion: The depth to which remaining
            directly recursive elements are expanded for non-regular (sub)
            grammars..
        :param compress_unions: If True, unions of single-char regexes
            will be compressed to range expressions.
        """

        self.grammar: CanonicalGrammar = canonical(grammar)
        self.max_num_expansions = max_num_expansions
        self.expansion_depth_direct_recursion = expansion_depth_direct_recursion
        self.compress_unions = compress_unions

    def to_regex(
        self, node_symbol: str = "<start>", convert_to_z3=True
    ) -> z3.ReRef | Regex:
        assert isinstance(node_symbol, str)

        result = convert_grammar_to_regex(
            self.grammar, node_symbol, do_compress_unions=self.compress_unions
        )

        return result if not convert_to_z3 else regex_to_z3(result)


@cache
def convert_grammar_to_regex(
    grammar: FrozenCanonicalGrammar,
    start_symbol: str = "<start>",
    do_compress_unions: bool = True,
    end_symbol: Optional[str] = None,
) -> Regex:
    """
    TODO: Document.

    Kudos to Rahul Gopinath for his blog entry:
    https://rahul.gopinath.org/post/2021/11/13/regular-grammar-to-regular-expression/

    >>> from grammar_to_regex.helpers import canonical
    >>> grammar = canonical(
    ...     {
    ...         "<start>": ["<A>"],
    ...         "<A>": ["a", "a<B><A>", "<B>a<A>"],
    ...         "<B>": ["b", "b<B>"],
    ...     }
    ... )
    >>> print(convert_grammar_to_regex(grammar))
    ((("a" • "b"* • "b") | ("b"* • "b" • "a"))* • "a")

    :param grammar:
    :param start_symbol:
    :param end_symbol:
    :param do_compress_unions:
    :return:
    """

    assert is_nonterminal(start_symbol)
    assert start_symbol in grammar
    assert end_symbol is None or is_nonterminal(end_symbol)

    regular_grammar, grammar_type = regularize_grammar(grammar)
    assert grammar_type in [LEFT_LINEAR, RIGHT_LINEAR, NON_RECURSIVE]

    if grammar_type == LEFT_LINEAR:
        return reverse_regex(convert_grammar_to_regex(reverse_grammar(regular_grammar)))

    closure: frozendict[str, FrozenOrderedSet[str]] = compute_closure(
        {fr: edges.values() for fr, edges in edges_in_grammar(grammar).items()}
    )

    if end_symbol is None:
        end_symbol, regular_grammar = add_end_symbol(regular_grammar, closure)

        closure = compute_closure(
            {
                fr: edges.values()
                for fr, edges in edges_in_grammar(regular_grammar).items()
            }
        )

    assert end_symbol in closure.get(start_symbol, ())

    # We solve the non-recursive nonterminals in each *reachable* rule.
    # On the way, we convert the terminal prefix of each expansion
    # alternative to a regex. As a result, all alternatives consist of
    # at most two elements: an optional regex and a nonterminal string.
    regular_grammar_with_regex_prefixes = convert_grammar_to_intermediate_grammar(
        regular_grammar, closure, start_symbol, end_symbol
    )

    assert end_symbol in regular_grammar_with_regex_prefixes
    assert is_intermediate_grammar(regular_grammar_with_regex_prefixes, end_symbol)

    # Compress prefixes.
    regular_grammar_with_union_prefixes = compress_prefixes_to_unions(
        regular_grammar_with_regex_prefixes, end_symbol
    )

    assert end_symbol in regular_grammar_with_union_prefixes
    assert is_intermediate_grammar(regular_grammar_with_union_prefixes, end_symbol)

    # Eliminate direct recursion.
    direct_recursion_free_grammar = eliminate_direct_recursion(
        regular_grammar_with_union_prefixes, end_symbol
    )
    assert end_symbol in direct_recursion_free_grammar
    assert is_intermediate_grammar(direct_recursion_free_grammar, end_symbol)

    resulting_grammar = direct_recursion_free_grammar
    while len(resulting_grammar) > 2:
        # Eliminate nonterminal symbols.
        symbol_to_eliminate = next(
            (
                nonterminal
                for nonterminal in resulting_grammar
                if nonterminal != start_symbol and nonterminal != end_symbol
            ),
            None,
        )
        assert symbol_to_eliminate is not None

        resulting_grammar = eliminate_direct_recursion(
            eliminate_symbol(resulting_grammar, symbol_to_eliminate, end_symbol),
            end_symbol,
        )

        assert is_intermediate_grammar(resulting_grammar, end_symbol)

    assert len(resulting_grammar) == 2
    assert start_symbol in resulting_grammar
    assert end_symbol in resulting_grammar
    assert all(
        alternative[-1] == end_symbol for alternative in resulting_grammar[start_symbol]
    )

    result = union(*(alternative[0] for alternative in resulting_grammar[start_symbol]))
    assert isinstance(result, Regex)

    return compress_unions(result) if do_compress_unions else result


def reverse_grammar(grammar: CanonicalGrammar) -> CanonicalGrammar:
    return frozendict(
        {
            key: tuple(tuple(reversed(alternative)) for alternative in alternatives)
            for key, alternatives in grammar.items()
        }
    )


def reverse_regex(regex: Regex) -> Regex:
    match regex:
        case Star(child):
            return Star(reverse_regex(child))
        case Union(children):
            return Union(tuple(reverse_regex(child) for child in children))
        case Concat(children):
            return Concat(tuple(reverse_regex(child) for child in reversed(children)))
        case _:
            return regex


def convert_grammar_to_intermediate_grammar(
    grammar: CanonicalGrammar,
    closure: frozendict[str, FrozenOrderedSet[str]],
    start_symbol: str,
    end_symbol: str,
    do_compress_unions: bool = True,
) -> IntermediateGrammar:
    return frozendict(
        {
            nonterminal: tuple(
                (
                    (
                        concat(
                            *(
                                (
                                    Singleton(symbol)
                                    if not is_nonterminal(symbol)
                                    else convert_grammar_to_regex(
                                        grammar, symbol, do_compress_unions, end_symbol
                                    )
                                )
                                for symbol in alternative[:-1]
                            )
                        ),
                        alternative[-1],
                    )
                    if nonterminal != end_symbol
                    else alternative
                )
                for alternative in alternatives
            )
            for nonterminal, alternatives in grammar.items()
            if nonterminal == start_symbol
            or nonterminal in closure.get(start_symbol, ())
        }
    )


def add_end_symbol(
    grammar: CanonicalGrammar, closure: frozendict[str, FrozenOrderedSet[str]]
) -> FrozenCanonicalGrammar:
    end_symbol = fresh_nonterminal(grammar, "<end>")

    grammar = frozendict(
        {
            nonterminal: tuple(
                (
                    tuple(alternative) + (end_symbol,)
                    if (
                        len(alternative) == 0
                        or not is_nonterminal(alternative[-1])
                        or nonterminal not in closure.get(alternative[-1], ())
                    )
                    else alternative
                )
                for alternative in alternatives
            )
            for nonterminal, alternatives in grammar.items()
        }
        | {end_symbol: ((epsilon(),),)}
    )

    return end_symbol, grammar


def eliminate_symbol(
    grammar: IntermediateGrammar, symbol_to_eliminate: str, end_symbol: str
) -> IntermediateGrammar:
    """
     That is, given

     ```
     A -> b B
       |  c D
     B -> e E
       |  f F
     ```

     Eliminating B will result in

     ```
     A -> b e E       # new
       |  b f F       # new
       |  c D
     B -> e E
       |  f F
    ```

    :param symbol_to_eliminate:
    :param grammar:
    :param end_symbol:
    :return:
    """

    grammar_after_elimination = frozendict()
    for nonterminal, alternatives in grammar.items():
        if nonterminal == symbol_to_eliminate:
            continue

        new_alternatives: Tuple[Tuple[Regex, str], ...] = ()
        for alternative in alternatives:
            if alternative[-1] != symbol_to_eliminate:
                new_alternatives += (alternative,)
                continue

            new_alternatives += tuple(
                (
                    concat(
                        *(alternative[:-1] + alternative_of_symbol_to_eliminate[:-1])
                    ),
                    alternative_of_symbol_to_eliminate[-1],
                )
                for alternative_of_symbol_to_eliminate in grammar[symbol_to_eliminate]
            )

        grammar_after_elimination = grammar_after_elimination.set(
            nonterminal, new_alternatives
        )

        assert is_intermediate_grammar(grammar_after_elimination, end_symbol)
    return grammar_after_elimination


def is_intermediate_grammar(
    regular_grammar_with_regex_prefixes: IntermediateGrammar,
    end_symbol: str,
) -> bool:
    return all(
        isinstance(alternatives, tuple)
        and isinstance(alternative, tuple)
        and (
            (nonterminal == end_symbol and alternatives == ((epsilon(),),))
            or (
                1 <= len(alternative) <= 2
                and isinstance(alternative[0], Regex)
                and isinstance(alternative[1], str)
            )
        )
        for nonterminal, alternatives in regular_grammar_with_regex_prefixes.items()
        for alternative in alternatives
    )


def compress_prefixes_to_unions(
    regular_grammar_with_regex_prefixes: IntermediateGrammar,
    end_symbol: str,
) -> frozendict[str, Tuple[Tuple[Regex, str] | Regex, ...]]:
    """
    <A> := a <B> | b <B> to (a|b) <B>

    :param regular_grammar_with_regex_prefixes:
    :param end_symbol:
    :return:
    """

    regular_grammar_with_union_prefixes = frozendict(
        {
            nonterminal: tuple(
                (
                    (epsilon(),)
                    if nonterminal == end_symbol
                    else (
                        union(*(alternative[0] for alternative in group)),
                        final_nonterminal,
                    )
                )
                for final_nonterminal, group in itertools.groupby(
                    alternatives, key=lambda alternative: alternative[-1]
                )
            )
            for nonterminal, alternatives in regular_grammar_with_regex_prefixes.items()
        }
    )
    return regular_grammar_with_union_prefixes


def eliminate_direct_recursion(
    regular_grammar_with_union_prefixes: IntermediateGrammar,
    end_symbol: str,
) -> IntermediateGrammar:
    """

    #
    # ```
    # A -> b B
    #    | c C
    #    | a A
    # ```
    #
    # becomes
    #
    # ```
    # A -> a* b B
    #    | a* c C
    # ```

    :param regular_grammar_with_union_prefixes:
    :param end_symbol:
    :return:
    """
    direct_recursion_free_grammar: IntermediateGrammar = frozendict()

    for nonterminal, alternatives in regular_grammar_with_union_prefixes.items():
        recursive_alternative = next(
            (
                alternative
                for alternative in alternatives
                if nonterminal == alternative[-1]
            ),
            None,
        )
        assert recursive_alternative is None or len(recursive_alternative) == 2

        if recursive_alternative is None:
            direct_recursion_free_grammar = direct_recursion_free_grammar.set(
                nonterminal, alternatives
            )
            continue

        direct_recursion_free_grammar = direct_recursion_free_grammar.set(
            nonterminal,
            tuple(
                (
                    concat(star(recursive_alternative[0]), alternative[0]),
                    alternative[-1],
                )
                for alternative in alternatives
                if alternative != recursive_alternative
            ),
        )

        assert is_intermediate_grammar(direct_recursion_free_grammar, end_symbol)

    return direct_recursion_free_grammar


def compress_unions(regex: Regex) -> Regex:
    """
    Compresses unions into ranges. We assume that all unions are flattened, i.e.,
    there are no unions directly nested inside unions.

    >>> compress_unions(union(Singleton("a"), Singleton("b"), Singleton("c")))
    Range(from_char='a', to_char='c')

    :param regex: The regex to compress.
    :return: The compressed regex.
    """

    match regex:
        case Union(children):
            # Compress single-char unions to ranges
            singletons = tuple(filter(Singleton.__instancecheck__, children))

            others = [
                compress_unions(child) for child in children if child not in singletons
            ]

            chars = frozendict({char_node.child: None for char_node in singletons})
            # NOTE: In some cases, string sequences that are longer than one char can appear in chars;
            #       for an XML grammar, e.g., escaped sequences like &quot; might appear.
            char_codes = sorted([ord(char) for char in chars if len(char) == 1])

            union_nodes = [
                (
                    Singleton(chr(group[0]))
                    if len(group) == 1
                    else Range(chr(group[0]), chr(group[-1]))
                )
                for group in consecutive_numbers(char_codes)
            ]
            union_nodes += others

            # NOTE: `longer_str` can also include the empty string.
            union_nodes.extend(
                [Singleton(longer_str) for longer_str in chars if len(longer_str) != 1]
            )

            return union(*union_nodes)
        case Star(child):
            return Star(compress_unions(child))
        case Concat(children):
            return concat(*[compress_unions(child) for child in children])
        case _:
            return regex
