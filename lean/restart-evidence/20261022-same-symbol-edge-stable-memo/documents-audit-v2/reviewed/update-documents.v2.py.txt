import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '__H9_SOURCE_SHA256__'
SOURCE_LINES = int('__H9_SOURCE_LINES__')
strict, full, audit_stem = '__H9_SELECTED_STRICT_STEM__', '__H9_SELECTED_FULL_STEM__', '__H9_AUDIT_STEM__'
metrics = {
    'actual_jobs': int('__H9_ACTUAL_JOBS__'),
    'source_jobs': int('__H9_SOURCE_JOBS__'),
    'audit_jobs': int('__H9_AUDIT_COMMANDS__'),
    'failed_jobs': int('__H9_FAILED_JOBS__'),
    'warned_source_exit_zero_jobs': int('__H9_WARNED_SOURCE_ZERO_JOBS__'),
    'rejected_public_type_jobs': int('__H9_REJECTED_PUBLIC_TYPE_JOBS__'),
    'audit_build_jobs': int('__H9_AUDIT_BUILD_JOBS__'),
    'audit_dependencies': int('__H9_AUDIT_DEPENDENCIES__'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '3c20d92660ea7ba40ce7e6c861f13b4fb5b11a03'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeStable.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '__H9_FULL_LOG_SHA256__'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / '__H9_FULL_READBACK_PATH__').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
assert '__H9_PUBLIC_TYPE_REVIEW__' == 'ROOT_AND_INDEPENDENT_COMPLETE'
head_specs = [
    ('completed_preserves', '__H9_COMPLETED_TYPE_SHA256__', '__H9_COMPLETED_TYPE_PATH__', '__H9_COMPLETED_PRINTED_TYPE_PATH__', '__H9_COMPLETED_AXIOMS_JSON__'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentSameSymbolEdgeStable.' + short
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
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '__H9_AUDIT_LOG_SHA256__'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Stable same-symbol pair memo

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-same-symbol-edge-stable-memo.md`.

SourceCurrentSameSymbolEdgeStable.completed_preserves is completed-past
preservation. It consumes an incoming Stable packet and the SAME observed
.call pair [] done equation. Operand residency and actual native growth,
result residency and canonical contextual EdgeLaw remain explicit inputs.
It derives final Stable, exact key links, captured operand residency,
all-returned cells, canonical presence, table extension and Returned.
It produces neither execution nor a result law, admission or WordRanges.
H8 supplies the native facts on both-miss calls. Hit-law identification
and actual stable-packet rebasing remain separate obligations.

EdgeLaw keeps the fixed view, model, ranks and holds. The independent
EdgeMeaning contract is not assigned a formal implication ordering here.
H6 constructed_node_calls remains the strongest combined semantic result.
Full public-pass behavior, convergence, practical host bounds, external
solver composition and Haskell refinement remain open.

All old proofs, drafts, counterexamples and optimized code remain.
Preservation covers 78951 baseline files/modes, 292 Haskell and 207 package
files. Only the Audit import and additive doc prefixes may change old
files. FINDINGS keeps the existing Haskell repair index FIRST. Work continues.
'''
findings = update
focused = f'''# Stable same-symbol pair memo

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

Stable is a packet at a completed comparison boundary. It retains exact
Nat-pair key links, captured operand residency, all-returned cells,
canonical presence, result residency and the canonical contextual EdgeLaw.
The fixed view, model, ranks and holds do not change with the current heap.
The public Stable declaration was reviewed directly in the source.

completed_preserves consumes the SAME actual .call pair [] done equation,
incoming Stable, requested operand residency, and the actual native
Extension, result residency and canonical contextual result law.
It derives final Stable, table extension and Returned for earlier cells.
The result retains the actual full checked state and separate pair memo.
The theorem does not produce execution, semantic admission, WordRanges,
a ready-hit law identification, or rebasing of the stable packet.

H8 both_miss_complete can supply the native facts for its both-miss case.
A ready hit does not run native edgeBody. Its historical law and captured
request must be identified by a later adapter, not by a fabricated Receipt.
Canonical storage avoids an assumed symmetry of execution. EdgeMeaning
is an independent closed-edge iff contract; no formal implication ordering
with contextual EdgeLaw is claimed. No EdgeProduced adapter is inferred.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Sole selected FULL: `{full}`.
Strict has a literal-empty log. Declaration limits remain unchanged.
FULL retains {len(raw)} raw bytes. The public theorem check/print TYPE bytes match.
{type_summary}
The complete public theorem TYPE was read by root and an independent reviewer.
All four private markers and the recorded actual helper names are absent
from TYPE. Private body names are permitted. The complete proof body remains
retained; no whole manual body read is claimed.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failed commands, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. All actual inputs, raw logs and exact
repair history remain. Metadata work creates no proof command.
Audit passes with {metrics['audit_build_jobs']} jobs and
{metrics['audit_dependencies']} theorem dependencies. Actual warnings
remain in the retained log. No seal or publication success is claimed here.

H6 constructed_node_calls remains the strongest combined semantic result.
Per-miss native admission and WordRanges, hit adapters, actual next-state
rebasing, sequence capacity, ruleOut, cluster control, recursive Mu,
the full withoutRedundantEdges pass and convergence remain open.
Practical fixed host width, external solver contracts/exported tables and
Haskell refinement remain open. No Haskell fix or runtime change is added.

Preservation covers all 78951 starting files/modes, 292 Haskell files and 207
active package files. All old proof components, drafts, counterexamples,
reproducers and optimized code remain. Only the Audit import and nine
additive document prefixes may change old files; old text has exact inverses.
The original Audit has 3114 lines and SHA 1d082f8610403a8c0fd6f11848020f915ff04f5bf7e60f72ba4bc3615041f5f6.
FINDINGS keeps the external repair index FIRST. The field-pool repair in
PR #65 and typing-documentation repair in PR #97 remain fixed. This checkpoint
requires no new Haskell repair. The whole formalization goal stays active.
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
note = ROOT / 'lean/notes-current-same-symbol-edge-stable-memo.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
