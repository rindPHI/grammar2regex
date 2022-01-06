from dataclasses import dataclass
from typing import Tuple

import z3


@dataclass(eq=True, frozen=True)
class Singleton:
    child: str

    def __str__(self):
        return "ε" if not self.child else f'"{self.child}"'


@dataclass(eq=True, frozen=True)
class Star:
    child: 'Regex'

    def __str__(self):
        return f"{self.child}*"


@dataclass(eq=True, frozen=True)
class Union:
    children: Tuple['Regex', ...]

    def __str__(self):
        return "(" + " | ".join(map(str, self.children)) + ")"


@dataclass(eq=True, frozen=True)
class Concat:
    children: Tuple['Regex', ...]

    def __str__(self):
        return "(" + " • ".join(map(str, self.children)) + ")"


@dataclass(eq=True, frozen=True)
class Range:
    from_char: str
    to_char: str

    def __str__(self):
        return f'["{self.from_char}" .. "{self.to_char}"]'


Regex = Singleton | Union | Concat | Range | Star


def epsilon() -> Regex:
    return Singleton("")


def union(*children: Regex) -> Regex:
    assert children

    if len(children) == 1:
        return children[0]

    union_elements = [child for child in children if isinstance(child, Union)]
    others = [child for child in children if not isinstance(child, Union)]

    flattened_children = [item for union_elem in union_elements for item in union_elem.children]
    flattened_children += others

    return Union(tuple(flattened_children))


def is_epsilon(regex: Regex) -> bool:
    return isinstance(regex, Singleton) and not regex.child


def concat(*children: Regex) -> Regex:
    children = [child for child in children if not is_epsilon(child)]

    if not children:
        return epsilon()

    if len(children) == 1:
        return children[0]

    elements = []
    for child in children:
        if isinstance(child, Concat):
            elements.extend(child.children)
            continue

        elements.append(child)

    return Concat(tuple(elements))


def star(child: Regex) -> Regex:
    if is_epsilon(child):
        return child

    return Star(child)


def regex_to_z3(regex: Regex) -> z3.ReRef:
    if isinstance(regex, Singleton):
        return z3.Re(regex.child)

    if isinstance(regex, Star):
        return z3.Star(regex_to_z3(regex.child))

    if isinstance(regex, Union):
        return z3.Union(*[regex_to_z3(child) for child in regex.children])

    if isinstance(regex, Concat):
        return z3.Concat(*[regex_to_z3(child) for child in regex.children])

    if isinstance(regex, Range):
        return z3.Range(regex.from_char, regex.to_char)

    assert False
