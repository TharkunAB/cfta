# pyright: strict
"""Prepare matched token and prefix fixtures from the pinned Qwen tokenizer."""

import argparse
import json
from pathlib import Path
from typing import TypedDict, cast

ALPHABET = frozenset("ab+*()")
EOS = 151643


class AddedToken(TypedDict):
    """One tokenizer special token."""

    id: int
    content: str


class TokenizerModel(TypedDict):
    """The input fields needed to extract BPE vocabulary IDs."""

    type: str
    vocab: dict[str, int]


class Tokenizer(TypedDict):
    """The input fields needed from the tokenizer JSON."""

    model: TokenizerModel
    decoder: dict[str, str | bool]
    added_tokens: list[AddedToken]


def terms(size: int, *, prefix: bool) -> tuple[set[str], set[str]]:
    """List expressions and atoms of exactly this node size."""
    atoms: set[str] = {"a", "b"} if size == 1 else set()
    if size >= 2:
        inner, _ = terms(size - 1, prefix=prefix)
        atoms.update(f"({term})" for term in inner)
    expressions = set(atoms)
    for left_size in range(1, size - 1):
        left, _ = terms(left_size, prefix=prefix)
        _, right = terms(size - 1 - left_size, prefix=prefix)
        expressions.update(
            op + lhs + rhs if prefix else lhs + op + rhs
            for lhs in left
            for rhs in right
            for op in "+*"
        )
    return expressions, atoms


def all_terms(size: int, *, prefix: bool) -> set[str]:
    """List expressions within a node budget."""
    return {term for n in range(1, size + 1) for term in terms(n, prefix=prefix)[0]}


def write_lines(path: Path, lines: list[str]) -> None:
    """Write one query or vocabulary entry per line, including empty prefixes."""
    path.write_text("".join(line + "\n" for line in lines), encoding="ascii")


def main() -> None:
    """Write the real token IDs and prefix sets."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tokenizer", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    output: Path = args.output
    tokenizer: Path = args.tokenizer
    data = cast(Tokenizer, json.loads(tokenizer.read_bytes()))
    if data["decoder"]["type"] != "ByteLevel" or data["model"]["type"] != "BPE":
        raise ValueError("expected the ByteLevel BPE tokenizer")
    # The ByteLevel mapping preserves every byte in this ASCII alphabet.
    vocab: dict[str, int] = data["model"]["vocab"]
    eligible = [(token, text) for text, token in vocab.items() if text and ALPHABET.issuperset(text)]
    if not any(entry["id"] == EOS and entry["content"] == "<|endoftext|>" for entry in data["added_tokens"]):
        raise ValueError("expected the configured end-of-text token")
    output.mkdir(parents=True, exist_ok=True)
    write_lines(output / "vocab.tsv", [f"{token}\t{text}" for token, text in sorted(eligible + [(EOS, "")])])
    for notation in ("infix", "prefix"):
        programs = all_terms(7, prefix=notation == "prefix")
        prefixes = sorted({term[:i] for term in programs for i in range(len(term) + 1)})
        write_lines(output / f"{notation}-exhaustive.txt", prefixes + ["x", ")", "ab)", "(x"])
        for size in (7, 15, 23):
            operators = (size - 1) // 2
            groups = size - 3
            left_chain = "+a*b" * (operators // 2)
            if notation == "infix":
                samples = ["a" + left_chain, "(" * groups + "a*b" + ")" * groups]
            else:
                count = 2 * (operators // 2)
                samples = ["+*" * (count // 2) + "a" + "ab" * (count // 2), "(" * groups + "*ab" + ")" * groups]
            work = sorted({term[:i] for term in samples for i in range(len(term) + 1)})
            write_lines(output / f"{notation}-{size}.txt", work)
        print(f"{notation}: {len(programs)} terms, {len(prefixes)} viable prefixes")
    print(f"{len(eligible)} eligible byte tokens of {len(vocab)} base IDs, plus EOS {EOS}")


if __name__ == "__main__":
    main()
