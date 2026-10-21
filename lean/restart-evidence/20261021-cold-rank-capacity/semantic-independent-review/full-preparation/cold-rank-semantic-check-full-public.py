"""Read the full cold constructed-node semantic theorem without running Lean or evaluating the numeric recurrence."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
PREFIX = "cold-rank-semantic-"
NAMESPACE = "MicroCFTA.SourceCurrentColdRankSemantic."
source = (HERE / "SourceCurrentColdRankSemantic.lean").read_text()
printer = (HERE / (PREFIX + "public-1.source.lean")).read_text()
raw = (HERE / (PREFIX + "public-1.log")).read_bytes()
log = raw.decode()
options = ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
assert printer.startswith(source)
for option in options:
    assert printer.count("set_option " + option) == 1, option
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
heads = [("constructed_initial_node_call", "theorem")]
markers = []
for head, _ in heads:
    name = NAMESPACE + head
    for directive in ["#check @", "#print ", "#print axioms "]:
        assert printer.count(directive + name) == 1, (directive, name)
    found = list(re.finditer(r"^(?:@)?" + re.escape(name) + r" :", log, re.M))
    assert len(found) == 1, (head, len(found))
    markers.append(found[0])
normalize = lambda text: "".join(text.split())
private = []
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
    assert "_private" not in checked + declared, head
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
        private_public_type_names=False, actual_axioms=sorted(axioms), actual_axioms_within_standard_allowed=True))
receipt = json.loads((HERE / (PREFIX + "public-1.json")).read_text())
assert receipt["exit_code"] == 0
print(json.dumps(dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(), source_lines=len(source.splitlines()),
    printer_sha256=hashlib.sha256(printer.encode()).hexdigest(), log_bytes=len(raw), log_sha256=hashlib.sha256(raw).hexdigest(),
    all_eight_printer_settings=True, no_omissions=True, heads=results, owned_public_job_exit=receipt["exit_code"],
    new_metadata_proof_jobs=0), indent=2))
