import re
from functools import cache
from itertools import groupby
from operator import itemgetter, sub
from typing import (
    List,
    TypeVar,
    Sequence,
    Tuple,
    Mapping,
    Iterable,
    Any,
)

from frozendict import frozendict

from grammar_to_regex.type_defs import (
    Grammar,
    CanonicalGrammar,
    FrozenOrderedSet,
    EdgeDict,
)

A = TypeVar("A")
B = TypeVar("B")

S = TypeVar("S")
T = TypeVar("T")


def split_expansion(expansion: str) -> List[str]:
    result = []

    token_start = 0
    token_start_backup = 0
    in_nonterminal = False

    for i in range(len(expansion)):
        if expansion[i] == "<":
            if in_nonterminal:
                in_nonterminal = False
            else:
                in_nonterminal = True
                result.append(expansion[token_start:i])
                token_start = i
        elif expansion[i] == " " and in_nonterminal:
            in_nonterminal = False
            token_start = token_start_backup
        elif expansion[i] == ">" and in_nonterminal:
            result.append(expansion[token_start : i + 1])
            in_nonterminal = False
            token_start = i + 1
            token_start_backup = token_start
        elif i == len(expansion) - 1:
            result.append(expansion[token_start : i + 1])

    return [token for token in result if token]


def reverse_grammar(grammar: Grammar) -> Grammar:
    return {
        key: [reverse_expansion(expansion) for expansion in expansions]
        for key, expansions in grammar.items()
    }


def reverse_expansion(expansion: str) -> str:
    return "".join(list(reversed(split_expansion(expansion))))


@cache
def is_nonterminal(element: str) -> bool:
    assert isinstance(
        element, str
    ), f"Expected string, got {type(element).__name__} ({element})"
    return RE_NONTERMINAL.match(element) is not None


def split_at_nonterminal_boundaries(expansion):
    return tuple(token for token in RE_NONTERMINAL.split(expansion) if token)


def canonical(grammar: Grammar) -> CanonicalGrammar:
    # Slightly optimized w.r.t. Fuzzing Book version: Call to split on
    # compiled regex instead of fresh compilation every time.

    return frozendict(
        {
            k: tuple(
                split_at_nonterminal_boundaries(expression)
                for expression in alternatives
            )
            for k, alternatives in grammar.items()
        }
    )


def non_canonical(grammar: CanonicalGrammar) -> Grammar:
    return frozendict(
        {
            k: tuple("".join(expansion) for expansion in alternatives)
            for k, alternatives in grammar.items()
        }
    )


RE_NONTERMINAL = re.compile(r"(<[^<> ]*>)")


def delete_unreachable(grammar: Grammar) -> Grammar:
    closure = compute_closure(
        {fr: edges.values() for fr, edges in edges_in_grammar(grammar).items()}
    )

    return frozendict(
        {
            nonterminal: alternatives
            for nonterminal, alternatives in grammar.items()
            if nonterminal == "<start>" or nonterminal in closure.get("<start>", ())
        }
    )


def consecutive_numbers(l: Sequence[int]) -> Tuple[Tuple[int, ...], ...]:
    """
    Groups the passed sequence into buckets of consecutive numbers.

    >>> consecutive_numbers([1, 2, 5, 6, 7, 10, 11, 12])
    ((1, 2), (5, 6, 7), (10, 11, 12))

    :param l: The sequence to group.
    :return: A tuple of tuples, each containing a group of consecutive numbers.
    """

    result: Tuple[Tuple[int, ...], ...] = ()

    for k, g in groupby(enumerate(l), lambda x: sub(*x)):
        result += (tuple(map(itemgetter(1), g)),)

    return result


def fresh_nonterminal(
    grammar: Grammar | CanonicalGrammar, suggestion: str = "<fresh>"
) -> str:
    assert is_nonterminal(suggestion)
    result = suggestion
    while result in grammar:
        result = "<" + result[1:-1] + "_" + ">"
    return result


def compute_closure(
    relation: Mapping[A, Iterable[B]]
) -> frozendict[A, FrozenOrderedSet[B]]:
    edges = frozendict(
        {a: frozendict({b: None for b in bs}) for a, bs in relation.items()}
    )

    # closure(A, B) :- edge(A, B).
    closure = edges

    changed = True
    while changed:
        changed = False

        # closure(A, C) :- edge(A, B), closure(B, C).
        for a in edges:
            for b in edges[a]:
                for c in closure[b]:
                    if c in closure[a]:
                        continue

                    changed = True
                    closure = closure.set(a, closure.get(a, frozendict()).set(c, None))

    return closure


def edges_in_grammar(grammar: Grammar | CanonicalGrammar) -> EdgeDict:
    if not is_canonical_grammar(grammar):
        grammar = canonical(grammar)

    return frozendict(
        {
            nonterminal: frozendict(
                {
                    (expansion_idx, symbol_idx): symbol
                    for expansion_idx, expansion in enumerate(expansions)
                    for symbol_idx, symbol in enumerate(expansion)
                    if symbol in grammar  # only consider nonterminals
                }
            )
            for nonterminal, expansions in grammar.items()
        }
    )


def is_canonical_grammar(grammar: Any) -> bool:
    return isinstance(grammar, Mapping) and all(
        isinstance(nonterminal, str)
        and isinstance(alternatives, Sequence)
        and all(
            isinstance(alternative, Sequence)
            and not isinstance(alternative, str)
            and isinstance(symbol, str)
            or len(type(symbol).__mro__) > 1
            and type(symbol).__mro__[1].__name__ == "Regex"
            for alternative in alternatives
            for symbol in alternative
        )
        for nonterminal, alternatives in grammar.items()
    )
