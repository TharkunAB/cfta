#!/usr/bin/env python3
"""Check complete retained Lean output contracts without running Lean."""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import re
from pathlib import Path


AREA = Path(__file__).resolve().parent
PARENT = "(edgesOf (.node parentEntry storedEdges depth free))"
PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSING = set(PAIRS.values())


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def top_split(text: str, separator: str) -> list[str]:
    """Split a contract only outside its explicitly delimited subexpressions."""
    stack: list[str] = []
    parts: list[str] = []
    start = 0
    for index, char in enumerate(text):
        if char in PAIRS:
            stack.append(PAIRS[char])
        elif char in CLOSING:
            assert stack and stack.pop() == char, f"Unbalanced delimiter at {index}"
        elif char == separator and not stack:
            parts.append(text[start:index].strip())
            start = index + 1
    assert not stack, "Unclosed delimiter in contract"
    parts.append(text[start:].strip())
    return parts


def outer(text: str) -> str:
    """Remove parentheses only when they enclose the complete expression."""
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        closes_early = False
        for index, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(text) - 1:
                    closes_early = True
                    break
        if closes_early:
            break
        text = text[1:-1].strip()
    return text


def output(path: Path, name: str) -> tuple[str, str, str]:
    source = path.read_text()
    start = re.search(r"\btheorem\s+" + re.escape(name) + r"\b", source)
    assert start, f"Missing theorem {name}: {path}"
    end = source.find(":= by", start.end())
    assert end != -1, f"Missing proof boundary for {name}"
    declaration = source[start.start():end]
    conclusion = re.search(r":\s*\n\s*(∃\b|∃\s)", declaration)
    assert conclusion, f"Missing existential result for {name}"
    result = declaration[conclusion.start() + 1:].strip()
    assert result.startswith("∃"), name
    parts = top_split(result[1:], ",")
    assert len(parts) >= 2, f"Missing existential body for {name}"
    # Later commas belong to undelimited quantifiers. Keep their exact scope.
    binders = parts[0]
    body = ",".join(parts[1:])
    return source, binders, body


def common(text: str) -> str:
    """Normalize only documented aliases and the generic callback binder form."""
    for before, after in (
        ("SourcePruningRecordTypes.Metadata", "Metadata"),
        ("EnumerationDriver.RenderStable", "RenderStable"),
        ("Queries", "SourceEndpointMemo.Memos"),
    ):
        text = re.sub(r"(?<![\w.])" + re.escape(before) + r"(?![\w])", after, text)
    # These two binder displays quantify the same recur, stop and order.
    text = re.sub(
        r"∀\s*\(\s*recur\s*:\s*([^()]*)\)\s*stop\s+order\s*,",
        r"∀ recur : \1, ∀ stop order,",
        text,
    )
    return re.sub(r"\s+", "", outer(text))


def specialized_main(text: str) -> str:
    text = re.sub(r"\bselectedEdges\b", PARENT, text)
    text = re.sub(r"\bbefore\b", "entered", text)
    return entry_counter(text)


def entry_counter(text: str) -> str:
    # This equality is an explicit output of the wrapper, not an assumption.
    text = re.sub(r"\bentered\s*\.\s*core\s*\.\s*counter\b", "before.core.counter", text)
    return common(text)


def equal(label: str, expected: str, observed: str) -> None:
    if expected != observed:
        delta = "\n".join(difflib.unified_diff(
            [expected], [observed], fromfile="retained original", tofile="actual wrapper", lineterm=""
        ))
        raise AssertionError(f"{label} differs:\n{delta}")


def uniform_parts(body: str) -> tuple[list[str], list[str]]:
    match = re.search(r"∀\s+extra\s*,", body)
    assert match, "Missing uniform extra-fuel quantifier"
    prefix = body[:match.start()].strip()
    assert prefix.endswith("∧"), "Missing conjunction before uniform callback output"
    return top_split(prefix[:-1], "∧"), top_split(body[match.end():], "∧")


def record(text: str) -> dict[str, object]:
    data = text.encode()
    return {"characters": len(text), "bytes": len(data), "sha256": sha(data)}


def save(path: Path, text: str) -> None:
    """Keep prior evidence exact when the validator is run again."""
    if path.exists():
        equal(str(path), text, path.read_text())
    else:
        path.write_text(text)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--ordinary", type=Path)
    parser.add_argument("--output-dir", type=Path, default=AREA / "contract-evidence")
    args = parser.parse_args()
    source_dir = args.repo.resolve() / "lean" / "MicroCFTA"
    ordinary = args.ordinary or source_dir / "SourcePruningEnumerationOrdinaryHookResources.lean"
    if not ordinary.exists() and args.ordinary is None:
        ordinary = AREA / ordinary.name
    paths = {
        "main": source_dir / "SourcePruningEnumerationHookResources.lean",
        "ordinary": ordinary,
        "callback_original": source_dir / "SourcePruningEnumerationRecursiveCallback.lean",
        "callback_augmented": source_dir / "SourcePruningEnumerationCallbackZero.lean",
    }
    sources: dict[str, str] = {}
    sources["main"], main_binders, main_body = output(paths["main"], "alternatives_zero_complete_resources")
    sources["ordinary"], ordinary_binders, ordinary_body = output(paths["ordinary"], "ordinary_zero_complete_resources")
    sources["callback_original"], old_binders, old_body = output(paths["callback_original"], "callback_complete")
    sources["callback_augmented"], new_binders, new_body = output(paths["callback_augmented"], "callback_zero_complete_resources")

    for key in ("main", "ordinary"):
        assert 'local notation "Result" => SourcePruningEnumerationNativeContinuations.Result' in sources[key]
    for key in ("callback_original", "callback_augmented"):
        assert 'local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult' in sources[key]

    # Every original main clause must occur as the complete final suffix.
    original_main = top_split(main_body, "∧")
    wrapper = top_split(ordinary_body, "∧")
    assert len(original_main) == 8, f"Unexpected original main clause count: {len(original_main)}"
    assert len(wrapper) == 16, f"Unexpected ordinary clause count: {len(wrapper)}"
    retained_main = wrapper[-len(original_main):]
    for index, (old, new) in enumerate(zip(original_main, retained_main, strict=True)):
        equal(f"main output clause {index + 1}", specialized_main(old), entry_counter(new))
    expected_main_binders = common(main_binders)
    actual_main_binders = common(ordinary_binders).replace("(entered:Cached)", "")
    equal("main existential witnesses", expected_main_binders, actual_main_binders)
    assert any(common(item) == "entered.core.counter=before.core.counter" for item in wrapper), \
        "Entry counter normalization lacks the explicit wrapper equality"

    # The augmented callback keeps all six initial facts and all three old
    # larger-fuel facts. The old generic forall is not replaced by resume0.
    old_prefix, old_uniform = uniform_parts(old_body)
    new_prefix, new_uniform = uniform_parts(new_body)
    assert (len(old_prefix), len(old_uniform)) == (6, 3)
    assert (len(new_prefix), len(new_uniform)) == (8, 4)
    for index, (old, new) in enumerate(zip(old_prefix, new_prefix[:6], strict=True)):
        equal(f"callback initial clause {index + 1}", common(old), common(new))
    for index, (old, new) in enumerate(zip(old_uniform, new_uniform[:3], strict=True)):
        equal(f"callback uniform clause {index + 1}", common(old), common(new))
    equal("original callback existential names", common(old_binders), "fuelresultafter")
    equal("augmented callback existential types", common(new_binders),
          "(fuel:Nat)(result:Bool×MetadataTyping)(after:Core)(outcome:Result)")

    normalized_main_old = "∧".join(specialized_main(item) for item in original_main)
    normalized_main_new = "∧".join(entry_counter(item) for item in retained_main)
    normalized_callback_old = "∧".join(common(item) for item in old_prefix) + "∧∀extra," + \
        "∧".join(common(item) for item in old_uniform)
    normalized_callback_new = "∧".join(common(item) for item in new_prefix[:6]) + "∧∀extra," + \
        "∧".join(common(item) for item in new_uniform[:3])
    equal("entire retained main output", normalized_main_old, normalized_main_new)
    equal("entire retained callback output", normalized_callback_old, normalized_callback_new)
    evidence = {
        "main-original-specialized.normalized.txt": normalized_main_old,
        "ordinary-retained-main.normalized.txt": normalized_main_new,
        "callback-original-retained.normalized.txt": normalized_callback_old,
        "callback-zero-retained.normalized.txt": normalized_callback_new,
    }
    report = {
        "status": "PASS",
        "scope": "Exact source-text output retention; Lean proof validation is separate.",
        "normalizations": [
            "Whitespace and complete-expression parentheses only.",
            "Metadata, RenderStable and Queries aliases; equivalent quantified recur binder display.",
            "Main selectedEdges := edgesOf (.node parentEntry storedEdges depth free).",
            "Main captured before := entered.",
            "entered.core.counter := before.core.counter, using the explicit wrapper output equality.",
            "Callback original inferred existential types agree with the augmented explicit types.",
        ],
        "sources": {key: {"path": str(paths[key].resolve()), **record(value)} for key, value in sources.items()},
        "main_output": {"retained_clauses": len(original_main), "ordinary_total_clauses": len(wrapper),
                        "retained_characters": len(normalized_main_old), **record(normalized_main_old)},
        "callback_output": {"retained_initial_clauses": len(old_prefix), "retained_uniform_clauses": len(old_uniform),
                            "generic_continueWith_retained": True, "retained_characters": len(normalized_callback_old),
                            **record(normalized_callback_old)},
        "artifacts": {name: record(value + "\n") for name, value in evidence.items()},
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, value in evidence.items():
        save(args.output_dir / name, value + "\n")
    save(args.output_dir / "report.json", json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
