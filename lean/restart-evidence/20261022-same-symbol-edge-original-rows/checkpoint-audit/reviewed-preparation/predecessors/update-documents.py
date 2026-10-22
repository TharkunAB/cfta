import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = 'de874220ae0aab490300f809c9fa4d2a931030fd69b95efb70deaa9a92a4b440'
SOURCE_LINES = int('44')
strict, full, audit_stem = 'direct-edge-word-ranges-strict-1', 'direct-edge-word-ranges-public-1', 'direct-edge-word-ranges-audit-1'
metrics = {
    'actual_jobs': int('3'),
    'source_jobs': int('2'),
    'audit_jobs': int('1'),
    'failed_jobs': int('0'),
    'warned_source_exit_zero_jobs': int('0'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3629'),
    'audit_dependencies': int('75380'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '108bc09e803b90b5e2e790c796d7ffd3c1d2f39f'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentAllocatedDirectEdgeWordRanges.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '601da48ea93ac39607b0dfcba89840530cacb5ac1d5127e67a0dbf01b1b7fb58'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/direct-edge-word-ranges-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
assert 'ROOT_AND_INDEPENDENT_COMPLETE' == 'ROOT_AND_INDEPENDENT_COMPLETE'
head_specs = [
    ('edge_body', 'dea801f02c35eb6ba68479e8fb93702264bf3b802aca8e06694683f988e9becf', 'public-readback/direct-edge-word-ranges-edge_body-public-type.txt', 'public-readback/direct-edge-word-ranges-edge_body-printed-public-type.txt', '["Classical.choice", "Quot.sound", "propext"]'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges.' + short
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
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '3fa06af51ce38d71a9b3774fc3c29e0e422ca4a8b27b8de4512de536e2994202'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Word ranges for direct edge-body prefixes

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-direct-edge-word-ranges.md`.

SourceCurrentAllocatedDirectEdgeWordRanges.edge_body derives WordRanges
for every raw Steps prefix of the exact empty-domain edgeBody request.
It uses the SAME Checked(bits+2) state, fixed source Facts, current Good,
SemanticReady, Grows, source history, exact EdgeScope and current EdgeReady.
Room uses source.nodes.next, source.edges.next, current domains.next and
literal mass 0. It does not supply runtime completion or a semantic law.

H11 semantic Completes remains a separate theorem. H6 constructed_node_calls
remains the strongest combined semantic result. Native completion, practical
host width, public Mu/full-pass and Haskell refinement remain open.
The whole formalization goal stays active and incomplete.

Preservation covers 82469 baseline files/modes, 298 baseline Haskell files,
207 active package files and all old evidence. Only the Audit import and
nine additive doc prefixes may change old files. FINDINGS retains its
Haskell repair index FIRST. Any new Haskell archive must match baseline bytes.
The preceding 108bc09e checkpoint is local only. Remote publication remains
PENDING_USER_APPROVAL after automatic review rejected earlier pushes.
This checkpoint publication tool performs no push or network command.
'''
findings = update
focused = f'''# Word ranges for direct edge-body prefixes

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

edge_body bounds every raw SourceEqualityNativeDemand.Steps prefix for
Control.edgeBody at the exact emptyDomain request and pure continuation.
It keeps the fixed source separate from the current populated checked state.
The premises are source Facts, current Good, SemanticReady, Grows and source
history, plus exact EdgeScope, current EdgeReady and one Room bound.
Room uses source node/edge counters and current domain count, with mass 0.
No source Fits, chosen instruction fuel, model, ranks, holds, Completes or
successful native run is assumed. This result proves word-range admission.
It does not prove native completion, result semantics, allocation totals,
physical language iff, practical width or the public Mu/full-pass result.
H11 semantic completion remains separate. H6 constructed_node_calls remains
the strongest combined semantic theorem. The whole goal remains incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Declaration limits remain unchanged.
FULL retains {len(raw)} raw bytes. Complete check/print TYPE bytes agree.
{type_summary}
Root and an independent reviewer read the complete public TYPE.
All four private markers and recorded helper names are absent from TYPE.
The complete proof body remains retained and checked programmatically.
No whole manual body read is claimed.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failed commands, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. Every actual input and raw log remains.
Metadata work creates no proof command. Audit passes with
{metrics['audit_build_jobs']} jobs and {metrics['audit_dependencies']} theorem
dependencies. The actual warning log remains. This writer does not claim
seal success, local publication success or remote publication success.

Preservation covers 82469 starting files/modes, 3627 older nonAudit Lean
sources, 298 baseline Haskell files and 207 active package files. Additional
H12 Haskell archives must match baseline live-source bytes under H12.
All old proof components, drafts, counterexamples and optimized code remain.
Only the Audit import and nine additive prefixes may change old files.
Every old document text has an exact inverse. The original Audit has 3117
lines and SHA eb67f7c671837d434cc443c9bbe48e2a11bd54c66a3ffbd3bb2506884face11e.
FINDINGS keeps the external repair index FIRST. PR #65 and PR #97 remain fixed.
No Haskell repair or runtime change is added.

The preceding 108bc09e checkpoint is LOCAL_ONLY. Earlier automatic approval
review rejected pushes. Continuing the goal is not fresh user approval.
The local publication tool preserves all seal, staging and filesystem/index/
HEAD checks. It records PENDING_USER_APPROVAL and performs no network command.
No cache reset, populated-state width cast or practical capacity claim is added.
Haskell/full-pass correspondence, convergence and host bounds remain open.
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
note = ROOT / 'lean/notes-current-direct-edge-word-ranges.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
