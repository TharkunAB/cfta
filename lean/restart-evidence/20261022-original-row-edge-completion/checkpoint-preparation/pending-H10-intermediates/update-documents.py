import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '__H10_SOURCE_SHA__'
SOURCE_LINES = int('__H10_SOURCE_LINES__')
strict, full, audit_stem = '__H10_SELECTED_STRICT__', '__H10_SELECTED_FULL__', '__H10_AUDIT_STEM__'
metrics = {
    'actual_jobs': int('__H10_ACTUAL_JOBS__'),
    'source_jobs': int('__H10_SOURCE_JOBS__'),
    'audit_jobs': int('__H10_AUDIT_JOBS__'),
    'failed_jobs': int('__H10_FAILED_JOBS__'),
    'warned_source_exit_zero_jobs': int('__H10_WARNED_SOURCE_EXIT_ZERO_JOBS__'),
    'rejected_public_type_jobs': int('__H10_REJECTED_PUBLIC_TYPE_JOBS__'),
    'audit_build_jobs': int('__H10_AUDIT_BUILD_JOBS__'),
    'audit_dependencies': int('__H10_AUDIT_DEPENDENCIES__'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == 'f985c09f5b18b740082799e15abc4736b3cbf880'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeReady.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '__H10_FULL_RAW_SHA__'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/same-symbol-edge-ready-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
assert '__H10_TYPE_REVIEW_STATUS__' == 'ROOT_AND_INDEPENDENT_COMPLETE'
head_specs = [
    ('ready_complete', '__H10_TYPE_SHA__', 'public-readback/same-symbol-edge-ready-ready_complete-public-type.txt', 'public-readback/same-symbol-edge-ready-ready_complete-printed-public-type.txt', '__H10_ACTUAL_AXIOMS_JSON__'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentSameSymbolEdgeReady.' + short
    assert head['check_print_type_identity'] and head['check_print_type_byte_identity'] and head['unique_complete_type_body_delimiter']
    checked = (HERE / type_path).read_bytes()
    assert checked == (HERE / printed_path).read_bytes() and hashlib.sha256(checked).hexdigest() == type_sha
    assert not any(marker in checked.decode() for marker in ['_private', '✝', '†', '‡']) and head['private_public_type_names'] is False
    assert head['actual_axioms'] == json.loads(axioms_json)
    assert head['actual_axioms_within_standard_allowed'] and set(head['actual_axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
    checked_types[short] = checked
proof_report = json.loads((HERE / 'proof-evidence-normal.json').read_text())
assert proof_report['status'] == 'PASS' and all(proof_report[key] == value for key, value in metrics.items())
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '__H10_AUDIT_SHA__'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Ready same-symbol comparisons

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-same-symbol-edge-ready.md`.

SourceCurrentSameSymbolEdgeReady.ready_complete derives execution from an
incoming Stable packet, current heap coherence, both requested resident
edges and presence of the original or reversed pair key. It returns the
actual value and full state at fixed execute fuel 7. The full checked state
is unchanged. The result is resident and satisfies the exact canonical
emptyDomain contextual EdgeLaw. Final Stable, table Extends and Returned
retain the pair memo. Original hits stop in 3 steps; reverse-only hits use 7.

The fixed view, model, ranks and holds remain unchanged. Captured operand
identity follows from resident records and coherence. No execution or
semantic symmetry, native Receipt or native admission is assumed on hits.
Both-miss native admission and completion remain separate H8 obligations.
H6 constructed_node_calls remains the strongest combined semantic result.
Full public-pass behavior, convergence, practical host bounds, external
solver composition and Haskell refinement remain open.

All old proofs, drafts, counterexamples and optimized code remain.
Preservation covers 80323 baseline files/modes, 292 unchanged baseline
Haskell files and 207 package files. New H10 Haskell archive copies must
match baseline bytes. Only the Audit import and additive doc prefixes may
change old files. FINDINGS keeps its Haskell repair index FIRST. Work continues.
'''
findings = update
focused = f'''# Ready same-symbol comparisons

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

ready_complete consumes a Stable packet at the same completed boundary,
current heap Coherent, both resident requested operands, and existence of
the original or reversed pair key. It derives an actual result and full
returned state at execute 7. The entire checked native and equality state
is unchanged. It retains the separate pair memo and its completed cells.
It derives result residency, the exact canonical emptyDomain contextual
EdgeLaw, final Stable, table Extends and Returned. It assumes no done
equation, result law or native admission for the ready comparison.

The original hit stops in 3 steps. The reverse-only case takes 7 steps.
Canonical presence forces descending requested identities in that case;
equal identities collapse the keys. Full captured operands follow from
key links, resident records and heap coherence. No EdgeLaw symmetry or
execution symmetry is used. A ready hit produces no native Receipt.
The fixed view, model, ranks and holds remain the same throughout.
A separate empty Stable producer is not added by this checkpoint.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Sole selected FULL: `{full}`.
Strict has a literal-empty log. Declaration limits remain unchanged.
FULL retains {len(raw)} raw bytes. The theorem check/print TYPE bytes match.
{type_summary}
The complete public theorem TYPE was read by root and an independent reviewer.
All four private markers and recorded helper names are absent from TYPE.
Private body names are permitted. The complete proof body remains retained;
no whole manual body read is claimed.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failed commands, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. Actual inputs, raw logs and exact repairs
remain. Metadata work creates no proof command. Audit passes with
{metrics['audit_build_jobs']} jobs and {metrics['audit_dependencies']} theorem
dependencies. The actual warning log remains. No seal or publication
success is claimed by this document writer.

H8 both_miss_complete retains its semantic interpreter completion,
current admission, readiness and WordRanges packet. This ready theorem
does not supply those facts or an all-pair completion theorem.
H6 constructed_node_calls remains the strongest combined semantic result.
Actual next-state rebasing, sequence capacity, ruleOut, cluster control,
recursive Mu, the full withoutRedundantEdges pass, convergence, practical
host width, solver contracts/exported tables and Haskell refinement remain
open. No Haskell fix or runtime change is added.

Preservation covers all 80323 starting files/modes, 292 baseline Haskell
files and 207 active package files. Additional H10 Haskell archive copies
must match pinned baseline live-source bytes and remain under H10.
All old proof components, drafts, counterexamples, reproducers and
optimized code remain. Only the Audit import and nine additive prefixes
may change old files; every old text has an exact inverse.
The original Audit has 3115 lines and SHA a36b1f2aefc14b99db041f7b8c40c6c3acc79db4f563b87532fda88b24d392fc.
FINDINGS keeps the external repair index FIRST. The field-pool repair in
PR #65 and typing-documentation repair in PR #97 remain fixed.
The whole formalization goal stays active.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
index = (ROOT / 'lean/restart-evidence/20261021-warm-next-packet/haskell-repair-index.md').read_text()
(HERE / 'haskell-repair-index.md').write_text(index)
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
        marker += index.rstrip() + '\n\n'
        assert original.startswith(marker)
        changed = marker + findings + '\n' + original[len(marker):]
        assert changed.startswith(marker + findings + '\n')
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.startswith(first + '\n\n' + update)
    assert changed.replace((findings if name == 'FINDINGS.md' else update) + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
note = ROOT / 'lean/notes-current-same-symbol-edge-ready.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
