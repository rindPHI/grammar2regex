import re
from typing import List

from fuzzingbook.Grammars import nonterminals

from grammar_to_regex.type_defs import Grammar


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
