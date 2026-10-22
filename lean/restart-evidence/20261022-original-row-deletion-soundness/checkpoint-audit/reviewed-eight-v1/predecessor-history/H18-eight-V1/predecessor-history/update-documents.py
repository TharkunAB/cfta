import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '__H17_SOURCE_SHA__'
SOURCE_LINES = int('__H17_SOURCE_LINES__')
strict, full, audit_stem = '__H17_SELECTED_STRICT_STEM__', '__H17_SELECTED_FULL_STEM__', '__H17_AUDIT_STEM__'
metrics = {
    'actual_jobs': int('__H17_ACTUAL_JOBS__'),
    'source_jobs': int('__H17_SOURCE_JOBS__'),
    'audit_jobs': int('__H17_AUDIT_JOBS__'),
    'failed_jobs': int('__H17_FAILED_JOBS__'),
    'warned_source_exit_zero_jobs': int('__H17_WARNED_SOURCE_EXIT_ZERO_JOBS__'),
    'rejected_public_type_jobs': int('__H17_REJECTED_PUBLIC_TYPE_JOBS__'),
    'audit_build_jobs': int('__H17_AUDIT_BUILD_JOBS__'),
    'audit_dependencies': int('__H17_AUDIT_DEPENDENCIES__'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '562120d456ea5836dc0f3cc718dafd25323521c3'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentOriginalRowClusterCompletion.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '__H17_FULL_LOG_SHA__'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/original-row-cluster-completion-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
head_specs = [
    ('cluster_complete', '__H17_CLUSTER_COMPLETE_TYPE_SHA__', 'public-readback/original-row-cluster-completion-cluster_complete-public-type.txt', 'public-readback/original-row-cluster-completion-cluster_complete-printed-public-type.txt', '__H17_CLUSTER_COMPLETE_ACTUAL_AXIOMS_JSON__'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentOriginalRowClusterCompletion.' + short
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
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '__H17_AUDIT_LOG_SHA__'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Completion of original-row clusters

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-original-row-cluster-completion.md`.

SourceCurrentOriginalRowClusterCompletion.cluster_complete derives an actual
H16 execute done equation for one exact original-parent symbol group.
The closed OriginalInput parent, source availability and current packet remain explicit.
The source, model, ranks, width, initial domain cache and initial reserve stay fixed.
The populated native state and pair memo evolve without reset.
Final rows retain original-group membership and a length bound.
The result retains current invariants, composable effects and the SAME global Trace.
No future comparison success, callback or future Room is a premise.
Promotion can change order. No ordered Sublist or physical pruning law is claimed.
The operational control is noncomputable. No compiled program or Haskell refinement is claimed.

H15 remains the per-comparison and domain-capacity foundation.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Generated parents, grouping, physical language iff, Mu/full traversal and the public pass remain open.
The overall goal is incomplete.

Preservation covers 88001 baseline files/modes, 298 baseline Haskell files
and 207 active package files. Only one Audit import and nine additive doc
prefixes may change old files. FINDINGS keeps its repair index FIRST.
The retained local payload through 562120d456 remains LOCAL_ONLY.
Remote publication is PENDING_USER_APPROVAL. This tool performs no network command.
'''
findings = update
focused = f'''# Completion of original-row clusters

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

cluster_complete derives an actual H16.execute done equation for one exact
symbol-filtered nodeEdges group of one available closed OriginalInput parent.
The source Facts, formulas, solver, public guard equality, view, model and ranks stay fixed.
Initial Good, Contextual, SemanticReady, Stable, native Idle, source growth,
issued history and the actual initial-to-current domain Trace remain explicit.
One fixed initial domain cache, Valid witness and conservative Room reserve support the run.
The native state and separate pair memo evolve at the same mathematical width.
No future comparison completion, callback, future Room, reset or desired semantic law is a premise.

H15 supplies each actual comparison and the next full current packet.
H16 comparison_lift selects its positive consumed prefix before the scan resumes.
The proof retains the candidate-first identity branch and promotion reconstruction order.
Generated common results select branches only. They never become later operands.
The outer cluster-length induction and inner scan-tail induction follow actual returned states.
The result is an actual execute equation, not an abstract call graph or a past-success adapter.

Every retained edge belongs to the original exact group; final length is at most its length.
Promotion can reorder rows. No ordered Sublist or pairwise maximality theorem is claimed.
The output retains Good, Contextual, SemanticReady, Stable, native Idle,
native Extension, pair-table Extends, Returned and the SAME initial-to-after domain Trace.
Effects compose at consecutive states. The history is not restarted at comparison entries.
The original reserve and returned Trace support later fixed-source current Room.
No new independent capacity forecast, semantic law or physical pruning iff is established.
The control remains noncomputable. No compiled runtime or Haskell refinement is claimed.

H15 remains the per-comparison and domain-capacity foundation.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Hash grouping order, generated-parent provenance, source/model rebase,
public Mu unfolding/kept-body, full traversal, practical width, solver contracts,
convergence and the public pass remain open. The goal stays incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Declaration limits remain unchanged.
FULL retains {len(raw)} raw bytes. Complete check/print TYPE bytes agree.
{type_summary}
Root and an independent reviewer read the complete checked public TYPE.
The printed TYPE is byte-identical. No second manual TYPE read is claimed.
All four private markers and recorded helper names are absent from TYPE.
The whole proof body is retained and checked programmatically.
No whole manual body read is claimed.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failures, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. Every actual input and raw log remains.
Metadata work creates no proof command. Audit has
{metrics['audit_build_jobs']} jobs and {metrics['audit_dependencies']} theorem
dependencies. This writer does not claim seal or publication success.

Preservation covers 88001 starting files/modes and 3632 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, old proofs,
drafts, counterexamples and optimized code remain.
Additional H17 Haskell archives must match baseline source bytes under H17.
Every old document has an exact inverse. The original Audit has 3122
lines and SHA 2fc4ad7d7e708d0601a46c6053f436be92e7fb03b7be78098ec66a2b9c86a698.
Its only edit is the new module import.
FINDINGS keeps the external repair index FIRST. PR #65 and PR #97 stay fixed.
No Haskell repair or runtime change is added.

The retained local payload through 562120d456 remains LOCAL_ONLY.
Earlier automatic approval review rejected pushes. Continuing is not fresh approval.
The local publisher keeps seal, staging and filesystem/index/HEAD checks.
It records PENDING_USER_APPROVAL and performs no network command.
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
note = ROOT / 'lean/notes-current-original-row-cluster-completion.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
