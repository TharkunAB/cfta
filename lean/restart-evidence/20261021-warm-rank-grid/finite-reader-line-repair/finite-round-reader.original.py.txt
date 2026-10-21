"""Read all finite-round public types and report their actual axiom sets."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
PREFIX = "finite-round-"
NAMESPACE = "MicroCFTA.SourceCurrentFiniteRoundForecast."
source = (HERE / "SourceCurrentFiniteRoundForecast.lean").read_text()
printer = (HERE / (PREFIX + "public-1.source.lean")).read_text()
raw = (HERE / (PREFIX + "public-1.log")).read_bytes()
log = raw.decode()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
assert printer.startswith(source)
heads = [("stage", "def"), ("fuelBounds", "def"), ("stage_bounds", "theorem")]
expected_tail = "\n" + "".join("set_option " + option + "\n" for option in options)
expected_tail += "".join(directive + NAMESPACE + head + "\n"
    for head, _ in heads for directive in ["#check @", "#print ", "#print axioms "])
assert printer[len(source):] == expected_tail
for option in options:
    assert printer.count("set_option " + option) == 1, option
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
markers = []
for head, _ in heads:
    name = NAMESPACE + head
    for directive in ["#check @", "#print ", "#print axioms "]:
        assert printer.count(directive + name) == 1, (directive, name)
    found = list(re.finditer(r"^(?:@)?" + re.escape(name) + r" :", log, re.M))
    assert len(found) == 1, (head, len(found))
    markers.append(found[0])
assert [marker.start() for marker in markers] == sorted(marker.start() for marker in markers)
normalize = lambda text: "".join(text.split())
private = ['grid', 'grid_member', 'caseSeed', 'caseSeeds', 'next', 'next_retains', 'next_case', 'stage_succ', 'stage_retains', 'boundsImage', 'fuel_member', 'fuel_limits']
private_markers = ("_private", "✝", "†", "‡")
results = []
for index, (head, kind) in enumerate(heads):
    name = NAMESPACE + head
    end = markers[index + 1].start() if index + 1 < len(heads) else len(log)
    segment = log[markers[index].end():end]
    delimiter = "\n" + kind + " " + name + " :"
    assert segment.count(delimiter) == 1, (head, "declaration delimiter")
    checked, printed = segment.split(delimiter, 1)
    axiom = re.search("'" + re.escape(name) + "' (depends on axioms:|does not depend on any axioms)", printed)
    assert axiom, (head, "axiom report")
    declaration, axiom_text = printed[:axiom.start()], printed[axiom.end():]
    expected = normalize(checked)
    candidates = []
    for match in re.finditer(r" :=\n", declaration):
        prefix = normalize(declaration[:match.start()])
        if prefix == expected:
            candidates.append(match)
        elif len(prefix) > len(expected):
            break
    assert len(candidates) == 1, (head, "unique complete TYPE/body delimiter", len(candidates))
    split = candidates[0]
    declared, body = declaration[:split.start()], declaration[split.end():]
    assert normalize(checked) == normalize(declared), head
    type_text = checked + declared
    type_tokens = re.findall(r"[^\s()\[\]{},:]+", type_text)
    private_names = sorted({token for token in type_tokens
        if any(marker in token for marker in private_markers)})
    assert not private_names, (head, "private TYPE markers", private_names)
    for helper in private:
        assert NAMESPACE + helper not in checked + declared, (head, helper)
    assert body.startswith("fun ") and len(body) > 50, head
    if axiom.group(1) == "depends on axioms:":
        report = re.match(r"\s*\[([^\]]*)\]", axiom_text)
        assert report, head
        axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in report.group(1).split(",") if item.strip()}
    else:
        axioms = set()
    assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, (head, axioms)
    results.append(dict(head=name, kind=kind, check_print_type_identity=True,
        checked_type_characters=len(checked), normalized_type_characters=len(normalize(checked)),
        unique_complete_type_body_delimiter=True, actual_body_starts_with="fun ", body_characters=len(body),
        private_type_markers_checked=list(private_markers), private_type_names=private_names,
        private_type_marker_scan_clean=not private_names, private_type_scope_review_required=bool(private_names),
        current_module_private_helpers_in_type=[], actual_axioms=sorted(axioms),
        actual_standard_three_axioms=axioms == {"propext", "Classical.choice", "Quot.sound"},
        actual_axioms_within_standard_allowed=True))
receipt = json.loads((HERE / (PREFIX + "public-1.json")).read_text())
assert receipt["exit_code"] == 0
print(json.dumps(dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(), source_lines=len(source.splitlines()),
    printer_sha256=hashlib.sha256(printer.encode()).hexdigest(), log_bytes=len(raw), log_sha256=hashlib.sha256(raw).hexdigest(),
    all_eight_printer_settings=True, diagnostic_limits_after_module_only=True,
    exact_complete_module_and_tail=True, no_omissions=True, heads=results,
    any_private_type_scope_review_required=any(result["private_type_scope_review_required"] for result in results),
    owned_public_job_exit=receipt["exit_code"],
    new_metadata_proof_jobs=0), indent=2))
