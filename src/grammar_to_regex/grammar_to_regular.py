import logging
from typing import Tuple, Mapping, Sequence, Optional, TypeVar, Literal

from frozendict import frozendict

from grammar_to_regex.helpers import (
    is_nonterminal,
    split_at_nonterminal_boundaries,
    compute_closure,
    edges_in_grammar,
)
from grammar_to_regex.type_defs import (
    CanonicalGrammar,
    FrozenCanonicalGrammar,
    EdgeDict,
    FrozenOrderedSet,
)

A = TypeVar("A")
B = TypeVar("B")
T = TypeVar("T")

LOGGER = logging.getLogger(__name__)


LEFT_LINEAR, RIGHT_LINEAR, NON_RECURSIVE = (
    "left-linear",
    "right-linear",
    "non-recursive",
)


def analyze_expansions(
    canonical_grammar: CanonicalGrammar,
    all_edges: Optional[EdgeDict] = None,
    closure: Optional[Mapping[str, FrozenOrderedSet[str]]] = None,
) -> Tuple[EdgeDict, EdgeDict, EdgeDict]:
    # Note: This function only reports recursive nonterminals, that is, those that
    #       reach the nonterminal on the left-hand side of the current grammar rule,
    #       if include_nonrecursive_expansions is False.
    all_edges = edges_in_grammar(canonical_grammar) if all_edges is None else all_edges
    closure = (
        compute_closure({fr: edges.values() for fr, edges in all_edges.items()})
        if closure is None
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

            # if not any(
            #         recursion_anchor in closure.get(recursion_anchor, {})
            #         for recursion_anchor in closure.get(to, {})
            # ):
            #     continue

            if fr not in closure.get(to, {}):
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
    from_nonterminal: str,
    closure: Mapping[str, FrozenOrderedSet[str]],
    allow_short_circuits: bool = False,
) -> Tuple[Tuple[str, ...], ...]:
    return tuple(
        tuple(expansion)
        for expansion in expansions
        if len(expansion) == 1
        or all(
            (allow_short_circuits and symbol == from_nonterminal)
            or from_nonterminal not in closure.get(symbol, {})
            # not any(
            #     rec_symbol in closure.get(rec_symbol, {})
            #     for rec_symbol in closure.get(symbol, {})
            # )
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
    expansion_depth: int = 3,
    expansion_depth_direct_recursion: int = 1,
) -> CanonicalGrammar:
    nonterminal_to_expand = grammar[nonterminal][expansion_idx][symbol_idx]

    nonterminal_expansions = bounded_expand_recursive_symbols(
        ((nonterminal_to_expand,),),
        nonterminal,
        grammar,
        closure,
        limit=expansion_depth,
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
        limit=expansion_depth_direct_recursion,
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
    expansion_depth: int = 3,
    expansion_depth_direct_recursion: int = 1,
) -> Tuple[
    FrozenCanonicalGrammar, Literal["left-linear", "right-linear", "non-recursive"]
]:
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
            grammar,
            closure,
            nonterminal,
            expansion_idx,
            symbol_idx,
            expansion_depth,
            expansion_depth_direct_recursion,
        )


def regularize_grammar(
    grammar: CanonicalGrammar,
    expansion_depth: int = 3,
    expansion_depth_direct_recursion: int = 1,
) -> Tuple[
    FrozenCanonicalGrammar, Literal["left-linear", "right-linear", "non-recursive"]
]:
    result, verdict = inline_nonregular_recursive_nonterminals(
        grammar, expansion_depth, expansion_depth_direct_recursion
    )
    assert verdict in [LEFT_LINEAR, RIGHT_LINEAR, NON_RECURSIVE]
    assert grammar_is_extended_regular(result, verdict)

    return result, verdict


def grammar_is_extended_regular(
    grammar: CanonicalGrammar,
    check_for_type: Literal["left-linear", "right-linear", "non-recursive"],
) -> bool:
    assert check_for_type in ["left-linear", "right-linear", "non-recursive"]

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
        or nonterminal not in closure.get(symbol, {})  # Non-recursive
        for nonterminal, alternatives in grammar.items()
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
