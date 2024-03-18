from typing import Mapping, Sequence

NonterminalType = str
Grammar = Mapping[str, Sequence[str]]
CanonicalGrammar = Mapping[str, Sequence[Sequence[str]]]
