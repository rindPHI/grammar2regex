from typing import Dict, List

NonterminalType = str
Grammar = Dict[NonterminalType, List[str]]
CanonicalGrammar = Dict[str, List[List[str]]]
