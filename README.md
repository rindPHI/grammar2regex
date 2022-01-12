# Grammar2Regex

Conversion of context-free grammars to regular expressions. Grammar2Regex can precisely convert regular
(left-linear / right-linear) grammars to regular expressions, either into a custom ADT format suitable
for further processing, or into ReRef objects of the z3 SMT solver.

Grammar2Regex can also convert arbitrary context-free grammars, which naturally comes with some loss of
information. In such cases, the tool "unwinds" the grammar up to a configurable depth, thus removing all
problematic expansions. The resulting regular expression represents a sub-language of the input grammar's
language.

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
print(converter.to_regex(convert_to_z3=False))
```

which yields an object of type grammar_to_regex.regex.Regex, in pretty print:

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
python3 setup.py sdist
pip3 install dist/grammar2regex-0.0.1.tar.gz
```

We recommend installation in a virtual environment, also since our requirements list pinned
version numbers. If you experience any problems with the pinned versions, feed free to find a working,
relaxed version and submit a pull request :)

## License and Maintainer

This project is licensed under the GNU GENERAL PUBLIC LICENSE v3.
It is maintained by [Dominic Steinhöfel](https://www.dominic-steinhoefel.de).