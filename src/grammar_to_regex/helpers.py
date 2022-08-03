import re
import typing
from itertools import groupby
from operator import itemgetter, sub
from typing import List, Set, Union, Dict

from grammar_to_regex.type_defs import Grammar, CanonicalGrammar


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
            result.append(expansion[token_start:i + 1])
            in_nonterminal = False
            token_start = i + 1
            token_start_backup = token_start
        elif i == len(expansion) - 1:
            result.append(expansion[token_start:i + 1])

    return [token for token in result if token]

    # return [token for token in re.split(RE_NONTERMINAL, expansion) if token]


def reverse_grammar(grammar: Grammar) -> Grammar:
    return {key: [reverse_expansion(expansion) for expansion in expansions]
            for key, expansions in grammar.items()}


def reverse_expansion(expansion: str) -> str:
    return "".join(list(reversed(split_expansion(expansion))))


def is_nonterminal(element: str) -> bool:
    """A little cheaper than regexes."""
    return element.startswith("<") and element.endswith(">") and " " not in element


class GrammarElem:
    def __init__(self, elem):
        self.elem = elem
        self.hash = None

    def __str__(self):
        return self.elem

    def __repr__(self):
        return f"{type(self).__name__}({self.elem})"

    def __hash__(self):
        if self.hash is None:
            self.hash = hash(repr(self))
        return self.hash

    def __eq__(self, other):
        if type(other) is not type(self):
            return False
        elif hash(other) == hash(self):
            return self.elem == other.elem
        else:
            return False


class Terminal(GrammarElem):
    def __init__(self, elem):
        super().__init__(elem)


class Nonterminal(GrammarElem):
    def __init__(self, elem):
        super().__init__(elem)


def str2grammar_elem(elem: str, cache: Union[None, Dict[str, GrammarElem]] = None) -> GrammarElem:
    if cache is not None and elem in cache:
        return cache[elem]

    if is_nonterminal(elem):
        result = Nonterminal(elem)
    else:
        result = Terminal(elem)

    if cache is None:
        return result
    else:
        cache: Dict[str, GrammarElem]
        return cache.setdefault(elem, result)


def canonical(grammar: Grammar) -> CanonicalGrammar:
    # Slightly optimized w.r.t. Fuzzing Book version: Call to split on
    # compiled regex instead of fresh compilation every time.
    def split(expansion):
        if isinstance(expansion, tuple):
            expansion = expansion[0]

        return [
            token
            for token in RE_NONTERMINAL.split(expansion)
            if token]

    return {
        k: [split(expression) for expression in alternatives]
        for k, alternatives in grammar.items()
    }


TypedCanonicalGrammar = Dict[GrammarElem, List[List[GrammarElem]]]


def grammar_to_typed_canonical(
        ordinary_grammar: Grammar,
        cache: Union[None, Dict[str, GrammarElem]] = None) -> TypedCanonicalGrammar:
    canonical_grammar = canonical(ordinary_grammar)
    typed_canonical_grammar = {}

    for key, expansions in canonical_grammar.items():
        typed_canonical_grammar[str2grammar_elem(key, cache)] = \
            [[str2grammar_elem(elem, cache) for elem in str_expansion]
             for str_expansion in expansions]

    return typed_canonical_grammar


def typed_canonical_to_grammar(typed_canonical_grammar: TypedCanonicalGrammar) -> Grammar:
    ordinary_grammar = {}

    for key, expansions in typed_canonical_grammar.items():
        ordinary_grammar[str(key)] = ["".join(map(str, expansion)) for expansion in expansions]

    return ordinary_grammar


def expand_nonterminals(grammar: Grammar,
                        start_symbol: str,
                        max_expansions: int,
                        allowed_nonterminals_str: Set[str],
                        prune: int = 5000) -> List[List[GrammarElem]]:
    result: List[List[GrammarElem]] = []

    cache: Dict[str, GrammarElem] = {start_symbol: Nonterminal(start_symbol)}

    to_expand: List[List[GrammarElem]] = [[cache[start_symbol]]]
    allowed_nonterminals = {str2grammar_elem(str_nonterminal, cache) for str_nonterminal in allowed_nonterminals_str}
    canonical_grammar = grammar_to_typed_canonical(grammar, cache)

    for _ in range(max_expansions):
        new_to_expand: List[List[GrammarElem]] = []
        for term in to_expand:
            to_eliminate: List[Nonterminal] = []
            for elem in term:
                if type(elem) is Nonterminal and \
                        not any(elem is x for x in to_eliminate) and \
                        not any(elem is x for x in allowed_nonterminals):
                    to_eliminate.append(typing.cast(Nonterminal, elem))

            if not to_eliminate and term not in result:
                result.append(term)
                continue

            nonterminal: Nonterminal
            for nonterminal in to_eliminate:
                expansion: List[GrammarElem]
                for expansion in canonical_grammar[nonterminal]:
                    new_to_expand_elem = [item for sublist in
                                          [expansion if elem is nonterminal else [elem] for elem in term] for
                                          item in sublist]
                    new_to_expand.append(new_to_expand_elem)

                    if len(new_to_expand) >= prune:
                        break

            if len(new_to_expand) >= prune:
                break

        to_expand = new_to_expand

    return [expansion for expansion in result
            if not any([elem for elem in expansion
                        if type(elem) is Nonterminal and
                        elem not in allowed_nonterminals])]


RE_NONTERMINAL = re.compile(r'(<[^<> ]*>)')


def nonterminals(expansion: str) -> List[str]:
    return RE_NONTERMINAL.findall(expansion)


def reachable_nonterminals(grammar: Grammar, _start_symbol: str = '<start>') -> Set[str]:
    reachable = set()

    def _find_reachable_nonterminals(grammar, symbol):
        nonlocal reachable
        reachable.add(symbol)
        for expansion in grammar.get(symbol, []):
            for nonterminal in nonterminals(expansion):
                if nonterminal not in reachable:
                    _find_reachable_nonterminals(grammar, nonterminal)

    _find_reachable_nonterminals(grammar, _start_symbol)
    return reachable


def unreachable_nonterminals(grammar: Grammar, _start_symbol='<start>') -> Set[str]:
    return grammar.keys() - reachable_nonterminals(grammar, _start_symbol)


def delete_unreachable(grammar):
    for unreachable in unreachable_nonterminals(grammar):
        del grammar[unreachable]


def consecutive_numbers(l: List[int]) -> List[List[int]]:
    result: List[List[int]] = []

    for k, g in groupby(enumerate(l), lambda x: sub(*x)):
        result.append(list(map(itemgetter(1), g)))

    return result
