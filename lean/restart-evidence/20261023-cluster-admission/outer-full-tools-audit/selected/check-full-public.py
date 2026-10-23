"""Read complete cluster admission public output. This script does not run Lean."""
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
assert 1 <= len(source.splitlines()) <= int("230")
namespace = "MicroCFTA.SourceCurrentOriginalRowClusterAdmission."
specs = json.loads('[["cluster_complete", "theorem"], ["completed_admitted", "theorem"]]')
public = re.findall(r"(?m)^\s*(?:(?:noncomputable|unsafe|partial)\s+)?(def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", source)
assert public == [(kind, short) for short, kind in specs]
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options)
for short, _kind in specs:
    tail += "".join(directive + namespace + short + "\n" for directive in ["#check @", "#print ", "#print axioms "])
assert source.rstrip().endswith("end MicroCFTA.SourceCurrentOriginalRowClusterAdmission")
assert not re.search(r"(?m)^\s*set_option\s+(?:maxRecDepth|maxHeartbeats)\b", source)
assert printer_raw == source_raw + tail.encode("utf-8")
for option in options:
    assert printer.splitlines().count("set_option " + option) == 1, option
for short, _kind in specs:
    for directive in ["#check @", "#print ", "#print axioms "]:
        assert printer.splitlines().count(directive + namespace + short) == 1
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
assert private == json.loads('[]'), "Only exact approved private declarations are permitted"
starts = []
for short, _kind in specs:
    name_pattern = re.escape(namespace + short) + r"(?:\.\{[^}\n]*\})?"
    found = list(re.finditer(r"^(?:@)?" + name_pattern + r" :", log, re.M))
    assert len(found) == 1, short
    starts.append(found[0])
assert starts == sorted(starts, key=lambda match: match.start()) and not log[:starts[0].start()].strip()
normalize = lambda text: re.sub(r"[ \t\r\n]+", " ", text).strip(" \t\r\n")
allowed = {"propext", "Classical.choice", "Quot.sound"}
artifacts, heads = {}, []
for index, (short, kind) in enumerate(specs):
    name = namespace + short
    segment = log[starts[index].end():starts[index + 1].start() if index + 1 < len(starts) else len(log)]
    name_pattern = re.escape(name) + r"(?:\.\{[^}\n]*\})?"
    delimiters = list(re.finditer(r"\n" + kind + " " + name_pattern + r" :", segment))
    assert len(delimiters) == 1, short
    checked, printed = segment[:delimiters[0].start()], segment[delimiters[0].end():]
    reports = list(re.finditer(r"^'" + re.escape(name) + r"' (depends on axioms:|does not depend on any axioms)", printed, re.M))
    assert len(reports) == 1, short
    axiom = reports[0]
    declaration, axiom_output = printed[:axiom.start()], printed[axiom.start():]
    expected, candidates = normalize(checked), []
    for match in re.finditer(r" :=\n", declaration):
        prefix = normalize(declaration[:match.start()])
        if prefix == expected:
            candidates.append(match)
        elif len(prefix) > len(expected):
            break
    assert len(candidates) == 1, short
    split = candidates[0]
    declared, body = declaration[:split.start()], declaration[split.end():]
    assert normalize(checked) == normalize(declared), short
    byte_identity = checked.encode("utf-8") == declared.encode("utf-8")
    for spelling in ["_private", "✝", "†", "‡"]:
        assert spelling not in checked + declared, ("private TYPE spelling", short, spelling)
    for helper in private:
        assert not re.search(re.escape(namespace + helper) + r"(?![\w'])", checked + declared), (short, helper)
    assert body.startswith("fun ") and len(body) > 50, short
    axiom_text = printed[axiom.end():]
    if axiom.group(1) == "depends on axioms:":
        report = re.fullmatch(r"\s*\[([^\]]*)\]\s*", axiom_text)
        assert report, short
        axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in report.group(1).split(",") if item.strip()}
    else:
        assert not axiom_text.strip(), short
        axioms = set()
    assert axioms <= allowed, (short, axioms)
    stem = "cluster-admission-outer-" + short
    artifacts.update({stem + "-public-type.txt": checked, stem + "-printed-public-type.txt": declared,
        stem + "-body.txt": body, stem + "-axioms.txt": axiom_output})
    heads.append(dict(head=name, kind=kind, check_print_type_identity=True, check_print_type_byte_identity=byte_identity,
        check_print_type_lexical_identity=True, checked_type_characters=len(checked), normalized_type_characters=len(expected),
        checked_type_bytes=len(checked.encode("utf-8")), checked_type_sha256=hashlib.sha256(checked.encode("utf-8")).hexdigest(),
        printed_type_characters=len(declared), printed_type_bytes=len(declared.encode("utf-8")),
        printed_type_sha256=hashlib.sha256(declared.encode("utf-8")).hexdigest(),
        canonical_type_sha256=hashlib.sha256(expected.encode("utf-8")).hexdigest(),
        unique_complete_type_body_delimiter=True, actual_body_starts_with="fun ", body_characters=len(body),
        private_public_type_names=False, private_type_spellings_checked=["_private", "✝", "†", "‡"],
        private_namespace_helpers_checked=private, actual_axioms=sorted(axioms),
        actual_axioms_within_standard_allowed=True, actual_standard_three_axioms=axioms == allowed))
result = dict(source_sha256=hashlib.sha256(source_raw).hexdigest(), source_lines=len(source.splitlines()),
    printer_sha256=hashlib.sha256(printer_raw).hexdigest(), log_bytes=len(raw), log_sha256=hashlib.sha256(raw).hexdigest(),
    all_eight_printer_settings=True, pp_option_count=7, linter_option_count=1, diagnostic_limit_count=2,
    exact_module_and_diagnostic_tail=True, diagnostic_limits_after_module_only=True, no_omissions=True,
    heads=heads, owned_public_job_exit=receipt["exit_code"], receipt_sha256=hashlib.sha256(args.receipt.read_bytes()).hexdigest(),
    configured_paths={key: str(getattr(args, key).resolve()) for key in ["source", "printer", "raw", "receipt"]},
    retained_slices={filename: dict(bytes=len(text.encode("utf-8")), sha256=hashlib.sha256(text.encode("utf-8")).hexdigest())
        for filename, text in artifacts.items()}, new_metadata_proof_jobs=0)
args.output_dir.mkdir(parents=True, exist_ok=True)
readback = args.output_dir / "cluster-admission-outer-full-readback.json"
assert not readback.exists() and all(not (args.output_dir / filename).exists() for filename in artifacts)
for filename, text in artifacts.items():
    (args.output_dir / filename).write_bytes(text.encode("utf-8"))
readback.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
