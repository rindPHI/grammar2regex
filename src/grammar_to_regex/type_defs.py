from typing import Mapping, Sequence, Tuple, TypeVar, TypeAlias

from frozendict import frozendict

NonterminalType: TypeAlias = str
Grammar: TypeAlias = Mapping[str, Sequence[str]]
CanonicalGrammar: TypeAlias = Mapping[str, Sequence[Sequence[str]]]
FrozenCanonicalGrammar: TypeAlias = frozendict[str, Tuple[Tuple[str, ...], ...]]

T = TypeVar("T")
FrozenOrderedSet: TypeAlias = frozendict[T, None]
EdgeDict: TypeAlias = frozendict[str, frozendict[Tuple[int, int], str]]
