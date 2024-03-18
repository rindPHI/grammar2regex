import logging
from typing import Tuple, Mapping, Sequence, Optional, TypeVar, Iterable, Literal

from frozendict import frozendict

from grammar_to_regex.helpers import (
    is_nonterminal,
    split_at_nonterminal_boundaries,
    star,
)
from grammar_to_regex.type_defs import CanonicalGrammar

A = TypeVar("A")
B = TypeVar("B")
T = TypeVar("T")
FrozenOrderedSet = frozendict[T, None]
LOGGER = logging.getLogger(__name__)

EdgeDict = frozendict[str, frozendict[Tuple[int, int], str]]


def edges_in_grammar(grammar: CanonicalGrammar) -> EdgeDict:
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


def analyze_expansions(
    canonical_grammar: CanonicalGrammar,
    all_edges: Optional[EdgeDict] = None,
    closure: Optional[Mapping[str, FrozenOrderedSet[str]]] = None,
    include_nonrecursive_expansions: bool = False,
) -> Tuple[EdgeDict, EdgeDict, EdgeDict]:
    # Note: This function only reports (indirectly) recursive nonterminals, that is,
    #       those that reach a nonterminal reaching itself, if include_nonrecursive_expansions
    #       is not set to true.
    all_edges = edges_in_grammar(canonical_grammar) if all_edges is None else all_edges
    closure = (
        compute_closure({fr: edges.values() for fr, edges in all_edges.items()})
        if closure is None and not include_nonrecursive_expansions
        else closure
    )

    left_recursive = frozendict({})
    right_recursive = frozendict({})
    central_recursive = frozendict({})

    assert len(canonical_grammar["<start>"]) == 1
    for fr, edges in all_edges.items():
        if fr == "<start>":
            continue

        for (expansion_idx, symbol_idx), to in edges.items():
            if len(canonical_grammar[fr][expansion_idx]) == 1:
                # A single nonterminal symbol is admissible in extended
                # regular grammars, even if it is recursive.
                assert canonical_grammar[fr][expansion_idx] != (
                    fr,
                ), f"Trivial recursion {fr} -> {fr} detected"
                continue

            if not include_nonrecursive_expansions and not any(
                recursion_anchor in closure.get(recursion_anchor, {})
                for recursion_anchor in closure.get(to, {})
            ):
                continue

            # Recursive expansion
            if len(canonical_grammar[fr][expansion_idx]) == 1 or (
                0 < symbol_idx < len(canonical_grammar[fr][expansion_idx]) - 1
            ):
                # A nonterminal symbol that is not at the beginning or end of
                # the expansion.
                central_recursive = edge_dict_set(
                    central_recursive, fr, expansion_idx, symbol_idx, to
                )
            elif symbol_idx == 0:
                left_recursive = edge_dict_set(
                    left_recursive, fr, expansion_idx, symbol_idx, to
                )
            else:
                assert symbol_idx == len(canonical_grammar[fr][expansion_idx]) - 1
                right_recursive = edge_dict_set(
                    right_recursive, fr, expansion_idx, symbol_idx, to
                )

    return left_recursive, right_recursive, central_recursive


def filter_recursive_expansions(
    expansions: Sequence[Sequence[str]],
    recursive_origin_nonterminal: str,
    closure: Mapping[str, FrozenOrderedSet[str]],
    allow_short_circuits: bool = False,
) -> Tuple[Tuple[str, ...], ...]:
    return tuple(
        tuple(expansion)
        for expansion in expansions
        if len(expansion) == 1
        or all(
            (allow_short_circuits and symbol == recursive_origin_nonterminal)
            or not any(
                rec_symbol in closure.get(rec_symbol, {})
                for rec_symbol in closure.get(symbol, {})
            )
            for symbol in expansion
        )
    )


def bounded_expand_recursive_symbols(
    expansions: Tuple[Tuple[str, ...], ...],
    recursion_origin: str,
    canonical_grammar: CanonicalGrammar,
    closure: Mapping[str, FrozenOrderedSet[str]],
    limit: int = 3,
    keep_short_circuits: bool = False,
) -> Tuple[Tuple[str, ...], ...]:
    for _ in range(limit):
        new_expansions = ()
        for expansion in expansions:
            current_new_expansions = ()
            for symbol in expansion:
                # We do *not* inline
                # - terminal symbols.
                # - the symbol `recursion_origin`, if `keep_short_circuits` is set
                #   (this is a direct recursive invocation).
                # - non-recursive nonterminals (i.e., nonterminals from which no
                #   symbol can be reached that can reach itself).
                if (
                    not is_nonterminal(symbol)
                    or (keep_short_circuits and symbol == recursion_origin)
                    or not any(
                        recursive_symbol in closure[recursive_symbol]
                        for recursive_symbol in closure[symbol]
                    )
                ):
                    current_new_expansions = tuple(
                        new_expansion + (symbol,)
                        for new_expansion in current_new_expansions or ((),)
                    )
                else:
                    current_new_expansions = tuple(
                        new_expansion + tuple(another_expansion)
                        for new_expansion in current_new_expansions or ((),)
                        for another_expansion in canonical_grammar[symbol]
                    )

            new_expansions += current_new_expansions

        expansions = new_expansions

    return expansions


def eliminate_recursive_expansion(
    grammar: CanonicalGrammar,
    closure: Mapping[str, FrozenOrderedSet[str]],
    nonterminal: str,
    expansion_idx: int,
    symbol_idx: int,
) -> CanonicalGrammar:
    nonterminal_to_expand = grammar[nonterminal][expansion_idx][symbol_idx]

    nonterminal_expansions = bounded_expand_recursive_symbols(
        ((nonterminal_to_expand,),),
        nonterminal,
        grammar,
        closure,
        limit=3,
        keep_short_circuits=True,
    )

    filtered_expansions = filter_recursive_expansions(
        nonterminal_expansions,
        nonterminal,
        closure,
        allow_short_circuits=True,
    )

    # All nonterminals in all expansions must either not be recursive or
    # be the nonterminal we are eliminating.
    assert all(
        symbol == nonterminal
        or not is_nonterminal(symbol)
        or nonterminal not in closure[symbol]
        for expansion in filtered_expansions
        for symbol in expansion
    ), filtered_expansions

    recursive_expansions = bounded_expand_recursive_symbols(
        filtered_expansions,
        nonterminal,
        grammar,
        closure,
        limit=1,
        keep_short_circuits=False,
    )

    filtered_nonrecursive_expansions = filter_recursive_expansions(
        recursive_expansions,
        nonterminal,
        closure,
        allow_short_circuits=False,
    )

    return merge_terminal_symbols(
        frozendict(
            {
                symbol: tuple(
                    new_expansion
                    for _expansion_idx, expansion in enumerate(expansions)
                    for new_expansion in (
                        (expansion,)
                        if symbol != nonterminal or expansion_idx != _expansion_idx
                        else (
                            tuple(expansion[:symbol_idx])
                            + nonrecursive_expansion
                            + tuple(expansion[symbol_idx + 1 :])
                            for nonrecursive_expansion in filtered_nonrecursive_expansions
                        )
                    )
                )
                for symbol, expansions in grammar.items()
            }
        )
    )


def inline_nonregular_recursive_nonterminals(
    grammar: CanonicalGrammar,
) -> Tuple[CanonicalGrammar, Literal["left-linear", "right-linear", "non-recursive"]]:
    assert all(
        all(
            isinstance(alternative, list) or isinstance(alternative, tuple)
            for alternative in alternatives
        )
        for alternatives in grammar.values()
    )

    verdict = 0

    while True:
        all_edges = edges_in_grammar(grammar)
        closure = compute_closure(
            {fr: edges.values() for fr, edges in all_edges.items()}
        )

        left_recursive, right_recursive, central_expansions = map(
            edge_dict_to_set, analyze_expansions(grammar, all_edges, closure)
        )

        if not central_expansions and (not left_recursive or not right_recursive):
            if not left_recursive and not right_recursive:
                assert verdict == 0
                verdict = 0
            elif right_recursive:
                assert verdict != 2
                verdict = 1
            else:
                assert left_recursive
                assert verdict != 1
                verdict = 2

            return grammar, (
                "non-recursive"
                if not verdict
                else ("right-linear" if verdict == 1 else "left-linear")
            )

        if central_expansions:
            to_eliminate = central_expansions
        elif len(left_recursive) <= len(right_recursive) and (verdict or 1) == 1:
            if verdict == 0:
                LOGGER.debug("Converting grammar to a right-linear regular grammar.")
            to_eliminate = left_recursive
            verdict = 1
        else:
            if verdict == 0:
                LOGGER.debug("Converting grammar to a left-linear regular grammar.")
            to_eliminate = right_recursive
            verdict = 2

        nonterminal, (expansion_idx, symbol_idx), symbol = next(iter(to_eliminate))
        LOGGER.debug(
            "Eliminating symbol %s at position %d in expansion `%s ::= %s`.",
            symbol,
            symbol_idx + 1,
            nonterminal,
            "".join(grammar[nonterminal][expansion_idx]),
        )

        grammar = eliminate_recursive_expansion(
            grammar, closure, nonterminal, expansion_idx, symbol_idx
        )


def inline_nonrecursive_nonregular_nonterminals(
    grammar: CanonicalGrammar,
    grammar_type: Literal["left-linear", "right-linear", "non-recursive"],
) -> CanonicalGrammar:
    while True:
        left_recursive, right_recursive, remaining_expansions = map(
            edge_dict_to_set,
            analyze_expansions(
                grammar, edges_in_grammar(grammar), include_nonrecursive_expansions=True
            ),
        )

        if remaining_expansions:
            to_eliminate = remaining_expansions
        elif left_recursive and grammar_type == "right-linear":
            to_eliminate = right_recursive
        elif right_recursive and grammar_type == "left-linear":
            to_eliminate = left_recursive
        else:
            break

        nonterminal, (expansion_idx, symbol_idx), symbol = next(iter(to_eliminate))

        grammar = merge_terminal_symbols(
            frozendict(
                {
                    key_nonterminal: tuple(
                        new_expansion
                        for _expansion_idx, expansion in enumerate(expansions)
                        for new_expansion in (
                            (expansion,)
                            if key_nonterminal != nonterminal
                            or expansion_idx != _expansion_idx
                            else (
                                tuple(expansion[:symbol_idx])
                                + tuple(nonrecursive_expansion)
                                + tuple(expansion[symbol_idx + 1 :])
                                for nonrecursive_expansion in grammar[symbol]
                            )
                        )
                    )
                    for key_nonterminal, expansions in grammar.items()
                }
            )
        )

    return grammar


def regularize_grammar(
    grammar: CanonicalGrammar, inline_nonrecursive_nonterminals: bool = False
) -> Tuple[CanonicalGrammar, Literal["left-linear", "right-linear", "non-recursive"]]:
    result, verdict = inline_nonregular_recursive_nonterminals(grammar)
    assert verdict in ["left-linear", "right-linear", "non-recursive"]
    assert grammar_is_extended_regular(
        result, verdict, nonrecursive_nonterminals_allowed=True
    )

    if not inline_nonrecursive_nonterminals:
        return result, verdict

    result = inline_nonrecursive_nonregular_nonterminals(result, verdict)
    assert grammar_is_extended_regular(result, verdict)

    return result, verdict


def grammar_is_extended_regular(
    grammar: CanonicalGrammar,
    check_for_type: Literal["left-linear", "right-linear", "non-recursive"],
    nonrecursive_nonterminals_allowed: bool = False,
) -> bool:
    assert check_for_type in ["left-linear", "right-linear", "non-recursive"]

    if nonrecursive_nonterminals_allowed:
        closure = compute_closure(
            {fr: edges.values() for fr, edges in edges_in_grammar(grammar).items()}
        )

    return all(
        len(alternative) == 1  # Single symbol
        or not is_nonterminal(symbol)  # Terminal
        or (
            symbol_idx == 0
            if check_for_type == "left-linear"
            else symbol_idx == len(alternative) - 1
        )  # Left or right-linear
        or (
            nonrecursive_nonterminals_allowed
            and not any(
                recursion_anchor in closure.get(recursion_anchor, {})
                for recursion_anchor in closure.get(symbol, {})
            )
        )  # Non-recursive
        for alternatives in grammar.values()
        for alternative in alternatives
        for symbol_idx, symbol in enumerate(alternative)
    )


def merge_terminal_symbols(grammar: CanonicalGrammar) -> CanonicalGrammar:
    """
    Merges successive terminal symbols in a grammar.

    >>> grammar = frozendict({
    ...     "<start>": (("<A>",),),
    ...     "<A>": (
    ...         ("a", "b", "c", "<A>", "<B>", "d ", "ef"),
    ...         ("abc", "de", "f"),
    ...         ("ab", "<A>")
    ...     ),
    ... })

    >>> dict(merge_terminal_symbols(grammar))
    {'<start>': (('<A>',),), '<A>': (('abc', '<A>', '<B>', 'd ef'), ('abcdef',), ('ab', '<A>'))}

    :param grammar: A grammar, which potentially contains expansions
        with successive terminal symbols.
    :return: A grammar without successsive strings consisting of terminal
        symbols in any alternative.
    """

    return frozendict(
        {
            nonterminal: tuple(
                split_at_nonterminal_boundaries("".join(alternative))
                for alternative in alternatives
            )
            for nonterminal, alternatives in grammar.items()
        }
    )


def edge_dict_to_set(
    edges: EdgeDict,
) -> FrozenOrderedSet[Tuple[str, Tuple[int, int], str]]:
    return frozendict(
        {
            (fr, (expansion_idx, symbol_idx), to): None
            for fr, out_edges in edges.items()
            for (expansion_idx, symbol_idx), to in out_edges.items()
        }
    )


def set_diff(a: FrozenOrderedSet[T], b: FrozenOrderedSet[T]) -> FrozenOrderedSet[T]:
    return frozendict({elem: None for elem in a if elem not in b})


def edge_dict_set(d: EdgeDict, fr: str, i: int, j: int, to: str) -> EdgeDict:
    return d.set(fr, d.get(fr, frozendict()).set((i, j), to))
