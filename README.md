# Grammar2Regex

Grammar2Regex converts context-free grammars to regular expressions.
Left- and right-linear grammars are always converted precisely.
Furthermore, some grammars with a regular language but a more general shape can also be converted.
For example, a rule `<N> ::= a<A><N>` is not right-linear due to the occurrence of `<A>`; but if `<A>` does not reach `<N>` and everything else is regular, we obtain a precise regular expression by computing the regular expression for `<A>` and inserting it into the rule for `<N>`.

For grammars with a non-regular language or a suboptimal shape, we "unwind" problematic expansion elements.
This step loses information, but enables us to compute under-approximating regular expressions for arbitrary context-free grammars.
Grammar2Regex returns expressions either in a custom ADT format suitable for further processing or as ReRef objects of the z3 SMT solver.

## Example

Consider the following grammar of XML attribute or tag name identifiers:

```python
import string
from typing import Dict, List
from fuzzingbook.Grammars import srange

xml_id_grammar: Dict[str, List[str]] = {
    "<start>": ["<id>"],
    "<id>": [
        "<id-no-prefix>",
        "<id-with-prefix>"
    ],
    "<id-no-prefix>": [
        "<id-start-char>",
        "<id-start-char><id-chars>",
    ],
    "<id-with-prefix>": ["<id-no-prefix>:<id-no-prefix>"],
    "<id-start-char>": srange("_" + string.ascii_letters),
    "<id-chars>": ["<id-char>", "<id-char><id-chars>"],
    "<id-char>": ["<id-start-char>"] + srange("-." + string.digits),
}
```

Our chosen grammar format is the one from the 
[Fuzzing Book](https://www.fuzzingbook.org/html/Grammars.html).

This grammar can be precisely converted into a regular expression:

```python
from grammar_to_regex.cfg2regex import RegexConverter

converter = RegexConverter(xml_id_grammar, compress_unions=True)
print(converter.to_regex('<start>', convert_to_z3=False))
```

which yields an object of type `grammar_to_regex.regex.Regex`, in pretty print:

```
((["-" .. "."] | ["0" .. "9"] | ["A" .. "Z"] | "_" | ["a" .. "z"])* • (["-" .. "."] | ["0" .. "9"] | ["A" .. "Z"] | "_" | ["a" .. "z"]))
```

You can also obtain an output in the regular expression format of the [z3 SMT solver](https://github.com/Z3Prover/z3)
if you need this for further processing (simply omit the `convert_to_z3=False` or set that parameter to
`True`).



## Installation

Grammar2Regex requires Python 3.10.

To install Grammar2Regex, run

```shell
pip install grammar2regex
```

To install it locally for testing, check this repository out and run

```shell
pip install -e .[test]
```

## License and Maintainer

This project is licensed under the GNU GENERAL PUBLIC LICENSE v3.
It is maintained by [Dominic Steinhöfel](https://www.dominic-steinhoefel.de).