"""Read complete H15 proof output. This script does not run Lean."""
from pathlib import Path
import argparse
import hashlib
import json
import re

parser = argparse.ArgumentParser(description=__doc__)
for argument in ["source", "printer", "raw", "receipt", "output-dir"]:
    parser.add_argument("--" + argument, type=Path, required=True)
parser.add_argument("--expected-source-sha256", required=True)
args = parser.parse_args()
assert re.fullmatch(r"[0-9a-f]{64}", args.expected_source_sha256)
source_raw, printer_raw, raw = (path.read_bytes() for path in [args.source, args.printer, args.raw])
source, printer, log = (item.decode("utf-8") for item in [source_raw, printer_raw, raw])
assert hashlib.sha256(source_raw).hexdigest() == args.expected_source_sha256
assert 1 <= len(source.splitlines()) <= 250
namespace = "MicroCFTA.SourceCurrentSameSymbolEdgeComparisonDomains."
name = namespace + "original_rows_complete"
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options)
tail += "".join(directive + name + "\n" for directive in ["#check @", "#print ", "#print axioms "])
assert source.rstrip().endswith("end MicroCFTA.SourceCurrentSameSymbolEdgeComparisonDomains")
assert not re.search(r"(?m)^\s*set_option\s+(?:maxRecDepth|maxHeartbeats)\b", source)
assert printer_raw == source_raw + tail.encode("utf-8")
for option in options:
    assert printer.splitlines().count("set_option " + option) == 1, option
for directive in ["#check @", "#print ", "#print axioms "]:
    assert printer.splitlines().count(directive + name) == 1, directive
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
receipt = json.loads(args.receipt.read_bytes())
assert receipt["exit_code"] == 0 and receipt["observed_at"]
assert (args.receipt.parent / receipt["source"]).resolve() == args.printer.resolve()
assert (args.receipt.parent / receipt["log"]).resolve() == args.raw.resolve()
assert receipt["sha256"] == hashlib.sha256(printer_raw).hexdigest()
assert Path(receipt["command"][-1]).resolve() == args.printer.resolve()
assert "-Dlinter.all=true" in receipt["command"]
private = []
for line in source.splitlines():
    if re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\b", line):
        declaration = re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\s+(?:(?:noncomputable|unsafe|partial)\s+)?(?:def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", line)
        assert declaration, ("unsupported private declaration", line)
        private.append(declaration.group(1))
found = list(re.finditer(r"^(?:@)?" + re.escape(name) + r" :", log, re.M))
assert len(found) == 1 and not log[:found[0].start()].strip()
segment = log[found[0].end():]
delimiter = "\ntheorem " + name + " :"
assert segment.count(delimiter) == 1
checked, printed = segment.split(delimiter, 1)
reports = list(re.finditer(r"^'" + re.escape(name) + r"' (depends on axioms:|does not depend on any axioms)", printed, re.M))
assert len(reports) == 1
axiom = reports[0]
declaration, axiom_output = printed[:axiom.start()], printed[axiom.start():]
normalize = lambda text: "".join(text.split())
expected, candidates = normalize(checked), []
for match in re.finditer(r" :=\n", declaration):
    prefix = normalize(declaration[:match.start()])
    if prefix == expected:
        candidates.append(match)
    elif len(prefix) > len(expected):
        break
assert len(candidates) == 1
split = candidates[0]
declared, body = declaration[:split.start()], declaration[split.end():]
assert checked.encode("utf-8") == declared.encode("utf-8")
for spelling in ["_private", "✝", "†", "‡"]:
    assert spelling not in checked + declared, ("private TYPE spelling", spelling)
for helper in private:
    assert not re.search(re.escape(namespace + helper) + r"(?![\w'])", checked + declared), helper
assert body.startswith("fun ") and len(body) > 50
axiom_text = printed[axiom.end():]
if axiom.group(1) == "depends on axioms:":
    report = re.fullmatch(r"\s*\[([^\]]*)\]\s*", axiom_text)
    assert report
    axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in report.group(1).split(",") if item.strip()}
else:
    assert not axiom_text.strip()
    axioms = set()
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert axioms <= allowed, axioms
artifacts = {"same-symbol-edge-comparison-domains-original_rows_complete-public-type.txt": checked,
    "same-symbol-edge-comparison-domains-original_rows_complete-printed-public-type.txt": declared,
    "same-symbol-edge-comparison-domains-original_rows_complete-body.txt": body, "same-symbol-edge-comparison-domains-original_rows_complete-axioms.txt": axiom_output}
head = dict(head=name, kind="theorem", check_print_type_identity=True, check_print_type_byte_identity=True,
    checked_type_characters=len(checked), normalized_type_characters=len(expected),
    unique_complete_type_body_delimiter=True, actual_body_starts_with="fun ", body_characters=len(body),
    private_public_type_names=False, private_type_spellings_checked=["_private", "✝", "†", "‡"],
    private_namespace_helpers_checked=private, actual_axioms=sorted(axioms),
    actual_axioms_within_standard_allowed=True, actual_standard_three_axioms=axioms == allowed)
result = dict(source_sha256=hashlib.sha256(source_raw).hexdigest(), source_lines=len(source.splitlines()),
    printer_sha256=hashlib.sha256(printer_raw).hexdigest(), log_bytes=len(raw), log_sha256=hashlib.sha256(raw).hexdigest(),
    all_eight_printer_settings=True, pp_option_count=7, linter_option_count=1, diagnostic_limit_count=2,
    exact_module_and_diagnostic_tail=True, diagnostic_limits_after_module_only=True, no_omissions=True,
    heads=[head], owned_public_job_exit=receipt["exit_code"], receipt_sha256=hashlib.sha256(args.receipt.read_bytes()).hexdigest(),
    configured_paths={key: str(getattr(args, key).resolve()) for key in ["source", "printer", "raw", "receipt"]},
    retained_slices={filename: dict(bytes=len(text.encode("utf-8")), sha256=hashlib.sha256(text.encode("utf-8")).hexdigest())
        for filename, text in artifacts.items()}, new_metadata_proof_jobs=0)
args.output_dir.mkdir(parents=True, exist_ok=True)
readback = args.output_dir / "same-symbol-edge-comparison-domains-full-readback.json"
assert not readback.exists() and all(not (args.output_dir / filename).exists() for filename in artifacts)
for filename, text in artifacts.items():
    (args.output_dir / filename).write_bytes(text.encode("utf-8"))
readback.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
