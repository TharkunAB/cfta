import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '__H11_SOURCE_SHA__'
SOURCE_LINES = int('__H11_SOURCE_LINES__')
strict, full, audit_stem = '__H11_SELECTED_STRICT__', '__H11_SELECTED_FULL__', '__H11_AUDIT_STEM__'
metrics = {
    'actual_jobs': int('__H11_ACTUAL_JOBS__'),
    'source_jobs': int('__H11_SOURCE_JOBS__'),
    'audit_jobs': int('__H11_AUDIT_JOBS__'),
    'failed_jobs': int('__H11_FAILED_JOBS__'),
    'warned_source_exit_zero_jobs': int('__H11_WARNED_SOURCE_EXIT_ZERO_JOBS__'),
    'rejected_public_type_jobs': int('__H11_REJECTED_PUBLIC_TYPE_JOBS__'),
    'audit_build_jobs': int('__H11_AUDIT_BUILD_JOBS__'),
    'audit_dependencies': int('__H11_AUDIT_DEPENDENCIES__'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '47c597a8e39cb82aa158a9fca104ed41b24849ef'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceRecursiveIntersectionOriginalRowCompletion.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '__H11_FULL_RAW_SHA__'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/original-row-edge-completion-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
assert '__H11_TYPE_REVIEW_STATUS__' == 'ROOT_AND_INDEPENDENT_COMPLETE'
head_specs = [
    ('edge_complete', '__H11_TYPE_SHA__', 'public-readback/original-row-edge-completion-edge_complete-public-type.txt', 'public-readback/original-row-edge-completion-edge_complete-printed-public-type.txt', '__H11_ACTUAL_AXIOMS_JSON__'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceRecursiveIntersectionOriginalRowCompletion.' + short
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
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '__H11_AUDIT_SHA__'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Semantic completion for original parent rows

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-original-row-edge-completion.md`.

SourceRecursiveIntersectionOriginalRowCompletion.edge_complete derives
Completes for the exact empty-domain edgeSemantic request. Its two literal
rows belong to actual available closed OriginalInput parents in the SAME
source heap with Facts. The theorem is generic in Symbol and Guard, with
arbitrary holds. The parents may coincide. No equal-symbol premise is used.
It assumes no semantic or native success and no FreeCorrect oracle.

Completes is existence of semantic interpreter fuel and an ok result.
This result does not produce native admission, WordRanges, a physical
language iff, the public Mu unfolding and kept-body branch, or the full public pass.
H6 constructed_node_calls remains the strongest combined semantic result.
Convergence, practical host bounds, external solver composition and
Haskell refinement remain open. The whole formalization goal stays active.

All old proofs, drafts, counterexamples and optimized code remain.
Preservation covers 81460 baseline files/modes, 298 unchanged baseline
Haskell files and 207 package files. Any new H11 Haskell archive copies
must match baseline bytes. Only the Audit import and additive doc prefixes
may change old files. FINDINGS retains its Haskell repair index FIRST.
'''
findings = update
focused = f'''# Semantic completion for original parent rows

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

edge_complete consumes one actual source heap and its Facts, two parent
values with OriginalInput witnesses, Available at that SAME source, empty
free lists, and literal row memberships in those parent values.
It derives Completes for edgeSemantic at the exact emptyDomain request
using those two edge records. This is generic in Symbol and Guard with
arbitrary holds. The parent values may be the same. The theorem requires
no equality of row symbols, semantic success, native success or caller
FreeCorrect oracle. Source Facts supply the view's free-correct law.

Completes states that some semantic interpreter fuel returns an ok result.
The proof uses finite-input bounds and the direct-row eventual execution
endpoint. It binds the OriginalInput witness to the actual available
parent by payload readback. Closed Mu values do not establish
closedness of every nested parent or arbitrary generated parent.

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

The theorem can discharge a semantic completion premise only after a
consumer identifies the same actual original closed parents and rows.
Native readiness, admission, WordRanges and actual execution still need
separate producers. No physical language iff, whole same-symbol scan,
cache rebasing, cluster reconstruction, the public Mu branch or full
withoutRedundantEdges result is produced by this theorem.
H6 constructed_node_calls remains the strongest combined semantic result.
Convergence, practical host width, external solver contracts/exported
tables and Haskell refinement remain open. No Haskell fix or runtime
change is added. The whole formalization goal stays active and incomplete.

Preservation covers all 81460 starting files/modes, 298 baseline Haskell
files and 207 active package files. Additional H11 Haskell archive copies
must match pinned baseline live-source bytes and remain under H11.
All old proof components, drafts, counterexamples, reproducers and
optimized code remain. Only the Audit import and nine additive prefixes
may change old files; every old text has an exact inverse.
The original Audit has 3116 lines and SHA d88c464169937b31eef6302946a736116e9449e14fdb965ec23ea49eb05bb769.
FINDINGS keeps the external repair index FIRST. The field-pool repair in
PR #65 and typing-documentation repair in PR #97 remain fixed.
No new Haskell repair is required by this checkpoint.
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
note = ROOT / 'lean/notes-current-original-row-edge-completion.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
