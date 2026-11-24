# pyright: strict
"""Test stack-conditioned whole-token transitions on two deterministic grammars."""

import argparse
from collections import defaultdict
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from resource import RUSAGE_SELF, getrusage
from time import process_time_ns
from typing import Literal, NamedTuple

from fixture import EOS, all_terms, write_lines

type Notation = Literal["infix", "prefix"]
type Vocabulary = dict[int, str]
type Rules = dict[str, tuple["Effect", ...]]


class Effect(NamedTuple):
    """Stack prefix to match and its replacement, top first."""

    pop: str
    push: str


@dataclass(frozen=True)
class State:
    """The required grammar symbols and the remaining node budget."""

    stack: str
    remaining: int


def rules_for(notation: Notation) -> Rules:
    """Compile the six byte transitions for the selected grammar."""
    if notation == "infix":
        # A needs an atom. T accepts another operator or ends the expression.
        # C closes a group. Reducing an inner T can consume C with the same byte.
        return {
            "a": (Effect("A", ""),),
            "b": (Effect("A", ""),),
            "+": (Effect("T", "AT"),),
            "*": (Effect("T", "AT"),),
            "(": (Effect("A", "ATC"),),
            ")": (Effect("TC", ""),),
        }
    atom = (Effect("E", ""), Effect("A", ""))
    operator = (Effect("E", "EA"),)
    return {
        "a": atom,
        "b": atom,
        "+": operator,
        "*": operator,
        "(": (Effect("E", "EC"), Effect("A", "EC")),
        ")": (Effect("C", ""),),
    }


def pending(stack: str) -> int:
    """Count the nodes still needed for a shortest completion."""
    return stack.count("A") + stack.count("E")


def compose(first: Effect, second: Effect) -> Effect | None:
    """Compose two effects when their known stack symbols agree."""
    overlap = min(len(first.push), len(second.pop))
    if first.push[:overlap] != second.pop[:overlap]:
        return None
    return Effect(first.pop + second.pop[overlap:], second.push + first.push[overlap:])


def cost(text: str) -> int:
    """Count the AST nodes introduced by the text."""
    return len(text) - text.count(")")


class Trie:
    """A vocabulary trie for the byte-wise comparison."""

    def __init__(self) -> None:
        self.children: dict[str, Trie] = {}
        self.tokens: list[int] = []


class StackIndex:
    """Token groups indexed by their required stack prefix."""

    def __init__(self) -> None:
        self.children: dict[str, StackIndex] = {}
        self.groups: list[tuple[int, list[int]]] = []


class Decoder:
    """One notation with three ways to make a token mask."""

    def __init__(self, notation: Notation, size: int, vocab: Vocabulary) -> None:
        self.initial = State("AT" if notation == "infix" else "E", size)
        self.done = "T" if notation == "infix" else ""
        self.rules = rules_for(notation)
        self.vocab = vocab

    @cached_property
    def trie(self) -> Trie:
        """Build the baseline index of vocabulary spellings."""
        trie = Trie()
        for token, text in self.vocab.items():
            if token == EOS:
                continue
            node = trie
            for char in text:
                if char not in node.children:
                    node.children[char] = Trie()
                node = node.children[char]
            node.tokens.append(token)
        return trie

    @cached_property
    def groups(self) -> list[tuple[str, int, list[int]]]:
        """Compose stack effects and share tests with the same condition."""
        groups: defaultdict[tuple[Effect, int], list[int]] = defaultdict(list)
        for token, text in self.vocab.items():
            if token == EOS:
                continue
            effects = {Effect("", "")}
            for char in text:
                effects = {
                    result
                    for first in effects
                    for second in self.rules.get(char, ())
                    if (result := compose(first, second)) is not None
                }
            for effect in effects:
                groups[effect, cost(text)].append(token)
        return [
            (effect.pop, need + pending(effect.push) - pending(effect.pop), ids)
            for (effect, need), ids in groups.items()
        ]

    @cached_property
    def stack_index(self) -> StackIndex:
        """Group vocabulary decisions by the stack symbols they inspect."""
        index = StackIndex()
        for pop, minimum, tokens in self.groups:
            node = index
            for symbol in pop:
                if symbol not in node.children:
                    node.children[symbol] = StackIndex()
                node = node.children[symbol]
            node.groups.append((minimum, tokens))
        return index

    def step(self, state: State, char: str) -> State | None:
        """Consume one character if it has a completion within the budget."""
        for pop, push in self.rules.get(char, ()):
            if state.stack.startswith(pop):
                stack = push + state.stack[len(pop) :]
                remaining = state.remaining - cost(char)
                return State(stack, remaining) if remaining >= pending(stack) else None
        return None

    def states(self, prefixes: list[str]) -> list[State | None]:
        """Resolve the query prefixes, sharing character work on common starts."""
        known: dict[str, State | None] = {"": self.initial}

        def state_of(text: str) -> State | None:
            if text not in known:
                parent = state_of(text[:-1])
                known[text] = None if parent is None else self.step(parent, text[-1])
            return known[text]

        return [state_of(text) for text in prefixes]

    def composed(self, state: State | None) -> list[int]:
        """Return the IDs admitted by the precomputed stack effects."""
        if state is None:
            return []
        slack = state.remaining - pending(state.stack)
        tokens = [EOS] if state.stack == self.done else []
        for pop, minimum, group in self.groups:
            if slack >= minimum and state.stack.startswith(pop):
                tokens.extend(group)
        return sorted(tokens)

    def indexed(self, state: State | None) -> list[int]:
        """Visit only groups whose pop condition matches the stack."""
        if state is None:
            return []
        slack = state.remaining - pending(state.stack)
        tokens = [EOS] if state.stack == self.done else []
        stack = iter(state.stack)
        node: StackIndex | None = self.stack_index
        while node is not None:
            for minimum, group in node.groups:
                if slack >= minimum:
                    tokens.extend(group)
            symbol = next(stack, None)
            node = None if symbol is None else node.children.get(symbol)
        return sorted(tokens)

    def bytewise(self, state: State | None) -> list[int]:
        """Return the same IDs through one byte-wise walk of the vocabulary trie."""
        if state is None:
            return []
        tokens = [EOS] if state.stack == self.done else []

        def visit(current: State, node: Trie) -> None:
            tokens.extend(node.tokens)
            for char, child in node.children.items():
                following = self.step(current, char)
                if following is not None:
                    visit(following, child)

        visit(state, self.trie)
        return sorted(tokens)


def load_vocabulary(path: Path) -> Vocabulary:
    """Read the tokenizer TSV, with an empty string only for EOS."""
    vocab: Vocabulary = {}
    for row in path.read_text(encoding="ascii").splitlines():
        ident, spelling = row.split("\t")
        vocab[int(ident)] = spelling
    if vocab.get(EOS) != "" or any(not text for i, text in vocab.items() if i != EOS):
        raise ValueError("expected one explicit EOS")
    return vocab


def verify(
    decoder: Decoder, notation: Notation, size: int, vocab: Vocabulary, prefixes: list[str]
) -> list[str]:
    """Compare both engines with the independent finite set of complete ASTs."""
    programs = all_terms(size, prefix=notation == "prefix")
    viable = {word[:i] for word in programs for i in range(len(word) + 1)}
    rows: list[str] = []
    for text, state in zip(prefixes, decoder.states(prefixes), strict=True):
        expected = sorted(
            token
            for token, continuation in vocab.items()
            if (token == EOS and text in programs) or (token != EOS and text + continuation in viable)
        )
        compiled = decoder.composed(state)
        bytewise = decoder.bytewise(state)
        indexed = decoder.indexed(state)
        if compiled != expected or bytewise != expected or indexed != expected:
            raise ValueError(
                f"{text!r}: expected {expected}, composed {compiled}, "
                f"bytewise {bytewise}, indexed {indexed}"
            )
        rows.append(",".join(map(str, expected)))
    return rows


def main() -> None:
    """Verify masks or measure a repeated batch without caching its answers."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("notation", choices=("infix", "prefix"))
    parser.add_argument("size", type=int)
    parser.add_argument("vocab", type=Path)
    parser.add_argument("prefixes", type=Path)
    parser.add_argument("mode", choices=("verify", "mask", "composed", "indexed", "bytewise"))
    parser.add_argument("--oracle", type=Path)
    parser.add_argument("--repeats", type=int, default=250)
    args = parser.parse_args()
    if args.size < 1 or args.repeats < 1:
        parser.error("size and repeats must be positive")
    notation: Notation = "prefix" if args.notation == "prefix" else "infix"
    vocab = load_vocabulary(args.vocab)
    prefixes = args.prefixes.read_text(encoding="ascii").splitlines()
    start = process_time_ns()
    decoder = Decoder(notation, args.size, vocab)
    if args.mode == "bytewise":
        _ = decoder.trie
    elif args.mode == "composed":
        _ = decoder.groups
    elif args.mode in ("indexed", "mask"):
        _ = decoder.stack_index
    compile_ns = process_time_ns() - start
    if args.mode == "verify":
        rows = verify(decoder, notation, args.size, vocab, prefixes)
        if args.oracle is not None:
            write_lines(args.oracle, rows)
        print(f"{notation} size={args.size}: {len(rows)} prefixes × {len(vocab)} IDs agree")
        return
    if args.mode == "mask":
        for state in decoder.states(prefixes):
            print(",".join(map(str, decoder.indexed(state))))
        return
    mask = {"composed": decoder.composed, "indexed": decoder.indexed, "bytewise": decoder.bytewise}[args.mode]

    def checksum(batch: list[State | None]) -> int:
        return sum(len(ids) + sum(ids) for state in batch if (ids := mask(state)))

    start = process_time_ns()
    states = decoder.states(prefixes)
    expected = checksum(states)
    first_batch_ns = process_time_ns() - start
    start = process_time_ns()
    total = sum(checksum(states) for _ in range(args.repeats))
    warm_ns = process_time_ns() - start
    if total != expected * args.repeats:
        raise ValueError("mask results changed during measurement")
    print(
        f"{notation} size={args.size} engine={args.mode} queries={len(states)} repeats={args.repeats} "
        f"groups={0 if args.mode == 'bytewise' else len(decoder.groups)} compile_cpu_ns={compile_ns} "
        f"first_batch_cpu_ns={first_batch_ns} warm_total_cpu_ns={warm_ns} checksum={expected} "
        f"peak_kib={getrusage(RUSAGE_SELF).ru_maxrss}"
    )


if __name__ == "__main__":
    main()
