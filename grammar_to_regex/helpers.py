import copy
import re
from typing import List, Set

from fuzzingbook.Grammars import nonterminals, unreachable_nonterminals

from grammar_to_regex.type_defs import Grammar, Nonterminal


def split_expansion(expansion: str) -> List[str]:
    nonterminal_symbols = nonterminals(expansion)

    if not nonterminal_symbols:
        return [expansion]

    for nonterminal_symbol in nonterminal_symbols:
        expansion = re.sub(f"({re.escape(nonterminal_symbol)})", '[cut]\\1[cut]', expansion)

    return [s for s in expansion.split("[cut]") if s]


def reverse_grammar(grammar: Grammar) -> Grammar:
    return {key: [reverse_expansion(expansion) for expansion in expansions]
            for key, expansions in grammar.items()}


def reverse_expansion(expansion: str) -> str:
    return "".join(list(reversed(split_expansion(expansion))))


def expand_nonterminals(grammar: Grammar,
                        start_symbol: Nonterminal,
                        max_expansions: int,
                        allowed_nonterminals: Set[Nonterminal]) -> List[str]:
    result: List[str] = []
    to_expand: List[str] = [start_symbol]

    for _ in range(max_expansions):
        new_to_expand: List[str] = []
        for term in to_expand:
            nonterminal_occurrences = set(nonterminals(term))
            to_eliminate = nonterminal_occurrences.difference(allowed_nonterminals)

            if not to_eliminate:
                result.append(term)
                continue

            for nonterminal in to_eliminate:
                for expansion in grammar[nonterminal]:
                    new_to_expand.append(term.replace(nonterminal, expansion))

        to_expand = new_to_expand

    return [expansion for expansion in result
            if not set(nonterminals(expansion)).difference(allowed_nonterminals)]


def delete_unreachable(grammar):
    for unreachable in unreachable_nonterminals(grammar):
        del grammar[unreachable]
