from dataclasses import dataclass
from typing import Tuple

import z3


@dataclass(frozen=True)
class Regex:
    pass


@dataclass(frozen=True)
class Singleton(Regex):
    child: str

    def __str__(self):
        return "ε" if not self.child else f'"{self.child}"'


@dataclass(frozen=True)
class Star(Regex):
    child: "Regex"

    def __str__(self):
        return f"{self.child}*"


@dataclass(frozen=True)
class Union(Regex):
    children: Tuple["Regex", ...]

    def __str__(self):
        return "(" + " | ".join(map(str, self.children)) + ")"


@dataclass(frozen=True)
class Concat(Regex):
    children: Tuple["Regex", ...]

    def __str__(self):
        return "(" + " • ".join(map(str, self.children)) + ")"


@dataclass(frozen=True)
class Range(Regex):
    from_char: str
    to_char: str

    def __str__(self):
        return f'["{self.from_char}" .. "{self.to_char}"]'


def epsilon() -> Regex:
    return Singleton("")


def union(*children: Regex) -> Regex:
    assert children
    assert all(isinstance(child, Regex) for child in children)

    if len(children) == 1:
        return children[0]

    union_elements = [child for child in children if isinstance(child, Union)]
    others = [child for child in children if not isinstance(child, Union)]

    flattened_children = [
        item for union_elem in union_elements for item in union_elem.children
    ]
    flattened_children += others

    return Union(tuple(flattened_children))


def is_epsilon(regex: Regex) -> bool:
    return isinstance(regex, Singleton) and not regex.child


def concat(*children: Regex) -> Regex:
    assert all(isinstance(child, Regex) for child in children)

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
    assert isinstance(child, Regex)

    if is_epsilon(child):
        return child

    return Star(child)


def regex_to_z3(regex: Regex) -> z3.ReRef:
    assert isinstance(regex, Regex)

    match regex:
        case Singleton(child):
            return z3.Re(child)
        case Star(child):
            return z3.Star(regex_to_z3(child))
        case Union(children):
            return z3.Union(*(regex_to_z3(child) for child in children))
        case Concat(children):
            return z3.Concat(*(regex_to_z3(child) for child in children))
        case Range(from_char, to_char):
            return z3.Range(from_char, to_char)
        case _:
            assert False, f"Unexpected regex type: {type(regex).__name__} ({regex})"
