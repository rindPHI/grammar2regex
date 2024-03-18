import itertools
import re
from functools import cache
from itertools import groupby
from operator import itemgetter, sub
from typing import (
    List,
    Set,
    Union,
    Dict,
    TypeVar,
    Iterable,
    Callable,
)

from frozendict import frozendict

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
            result.append(expansion[token_start : i + 1])
            in_nonterminal = False
            token_start = i + 1
            token_start_backup = token_start
        elif i == len(expansion) - 1:
            result.append(expansion[token_start : i + 1])

    return [token for token in result if token]

    # return [token for token in re.split(RE_NONTERMINAL, expansion) if token]


def reverse_grammar(grammar: Grammar) -> Grammar:
    return {
        key: [reverse_expansion(expansion) for expansion in expansions]
        for key, expansions in grammar.items()
    }


def reverse_expansion(expansion: str) -> str:
    return "".join(list(reversed(split_expansion(expansion))))


@cache
def is_nonterminal(element: str) -> bool:
    return RE_NONTERMINAL.match(element) is not None


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


def str2grammar_elem(
    elem: str, cache: Union[None, Dict[str, GrammarElem]] = None
) -> GrammarElem:
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


TypedCanonicalGrammar = Dict[GrammarElem, List[List[GrammarElem]]]


def grammar_to_typed_canonical(
    ordinary_grammar: Grammar, cache: Union[None, Dict[str, GrammarElem]] = None
) -> TypedCanonicalGrammar:
    canonical_grammar = canonical(ordinary_grammar)
    typed_canonical_grammar = {}

    for key, expansions in canonical_grammar.items():
        typed_canonical_grammar[str2grammar_elem(key, cache)] = [
            [str2grammar_elem(elem, cache) for elem in str_expansion]
            for str_expansion in expansions
        ]

    return typed_canonical_grammar


def typed_canonical_to_grammar(
    typed_canonical_grammar: TypedCanonicalGrammar,
) -> Grammar:
    ordinary_grammar = {}

    for key, expansions in typed_canonical_grammar.items():
        ordinary_grammar[str(key)] = [
            "".join(map(str, expansion)) for expansion in expansions
        ]

    return ordinary_grammar


RE_NONTERMINAL = re.compile(r"(<[^<> ]*>)")


def nonterminals(expansion: str) -> List[str]:
    return RE_NONTERMINAL.findall(expansion)


def reachable_nonterminals(
    grammar: Grammar, _start_symbol: str = "<start>"
) -> Set[str]:
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


def unreachable_nonterminals(grammar: Grammar, _start_symbol="<start>") -> Set[str]:
    return grammar.keys() - reachable_nonterminals(grammar, _start_symbol)


def delete_unreachable(grammar):
    for unreachable in unreachable_nonterminals(grammar):
        del grammar[unreachable]


def consecutive_numbers(l: List[int]) -> List[List[int]]:
    result: List[List[int]] = []

    for k, g in groupby(enumerate(l), lambda x: sub(*x)):
        result.append(list(map(itemgetter(1), g)))

    return result


S = TypeVar("S")
T = TypeVar("T")


def dict_of_lists_to_list_of_dicts(
    dict_of_lists: Dict[S, Iterable[T]]
) -> List[Dict[S, T]]:
    keys = list(dict_of_lists.keys())
    list_of_values = [dict_of_lists[key] for key in keys]
    product = list(itertools.product(*list_of_values))

    return [dict(zip(keys, product_elem)) for product_elem in product]


def grammar_to_frozen(grammar: Grammar) -> Grammar:
    if isinstance(grammar, frozendict):
        return grammar
    return frozendict({k: tuple(v) for k, v in grammar.items()})


def grammar_to_mutable(grammar: Grammar) -> Grammar:
    if not isinstance(grammar, frozendict):
        assert isinstance(grammar, dict)
        return grammar
    return {k: list(v) for k, v in grammar.items()}


def star(f: Callable[..., T], do_flatten=False) -> Callable[..., T]:
    """
    Transforms a function accepting n arguments into one accepting a sequence of n
    elements. If :code:`do_flatten` is True, the returned function accepts multiple
    arguments. Sequences in these arguments are flattened.

    Example
    -------

    Transforming a function adding two numbers to a function adding the two elements
    of a list of numbers:

    >>> star(lambda a, b: a + b)([1, 2])
    3

    Transforming a function adding four numbers to a function adding all passed numbers
    or their elements using flattening. There must be exactly four numbers in the
    given arguments.

    >>> star(lambda a, b, c, d: a + b + c + d, do_flatten=True)(1, [2, 3], 4)
    10

    It does not matter if the passed arguments are inside a list or not:

    >>> star(lambda a, b, c, d: a + b + c + d, do_flatten=True)([1], 2, [3, 4])
    10

    But we must pass exactly five numbers:

    >>> star(lambda a, b, c, d: a + b + c + d, do_flatten=True)(1, [2, 3, 4], 5)
    Traceback (most recent call last):
    ...
    TypeError: <lambda>() takes 4 positional arguments but 5 were given

    :param f: The function to be "starred."
    :param do_flatten: Set to True if the returned function should accept multiple
        arguments that are flattened before forwarding them to the original function.
    :return: The "starred" function.
    """

    if do_flatten:
        return lambda *x: f(*flatten(x))
    else:
        return lambda x: f(*x)
