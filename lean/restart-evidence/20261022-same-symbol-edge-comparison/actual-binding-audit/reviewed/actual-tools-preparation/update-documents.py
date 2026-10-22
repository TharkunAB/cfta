import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '02d01576ce9e7188342835138452a5163b150e28c264c01782137848e1a1c560'
SOURCE_LINES = int('112')
strict, full, audit_stem = 'same-symbol-edge-comparison-strict-1', 'same-symbol-edge-comparison-public-1', 'same-symbol-edge-comparison-audit-1'
metrics = {
    'actual_jobs': int('3'),
    'source_jobs': int('2'),
    'audit_jobs': int('1'),
    'failed_jobs': int('0'),
    'warned_source_exit_zero_jobs': int('0'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3631'),
    'audit_dependencies': int('75384'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '1d5a07b762950272e53c9bd2d5f478d7be39dfad'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeComparison.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '61cf4903d08f2d93443807fbb8429b6dbba821cc92910509d74a5404f905334d'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/same-symbol-edge-comparison-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
head_specs = [
    ('original_rows_complete', '7fb94c311d5eff9aa93faa2dab7cc235a2e9dffe365b98d2c5ca04c39c49dd8d', 'public-readback/same-symbol-edge-comparison-original_rows_complete-public-type.txt', 'public-readback/same-symbol-edge-comparison-original_rows_complete-printed-public-type.txt', '["Classical.choice", "Quot.sound", "propext"]'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentSameSymbolEdgeComparison.' + short
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
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '7e8be4569d2e14ecf95f0ac83511e8ca6e569dde6c70dbb761c51782f386af0b'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Completion across same-symbol pair-cache branches

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-same-symbol-edge-comparison.md`.

SourceCurrentSameSymbolEdgeComparison.original_rows_complete derives an
actual comparison result for ready and absent pair-cache branches.
It keeps the SAME source, models, populated checked state and pair memo.
Available closed OriginalInput parents, literal same-symbol rows, Stable,
current Good, Contextual, SemanticReady, native Idle, source growth/history
and one current Room remain explicit. No cache-branch premise is required.
The result retains residency, canonical conditional EdgeLaw, Good, Contextual,
SemanticReady, native Extension, Stable, native Idle, table Extends and Returned.
A ready hit has no native Receipt claim. No post-Room or future capacity follows.

H6 constructed_node_calls remains the strongest combined semantic theorem.
Generated-parent provenance, source/model rebase, physical language iff,
public Mu/full-pass and Haskell refinement remain open. The goal is incomplete.

Preservation covers 84279 baseline files/modes, 298 baseline Haskell files
and 207 active package files. Only one Audit import and nine additive doc
prefixes may change old files. FINDINGS keeps its repair index FIRST.
The preceding 1d5a07b7 checkpoint is LOCAL_ONLY. Remote publication remains
PENDING_USER_APPROVAL. This tool performs no push or network command.
'''
findings = update
focused = f'''# Completion across same-symbol pair-cache branches

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

original_rows_complete derives an actual wrapper comparison result across
original-ready, reverse-ready and both-miss pair-cache cases.
The requested edges are literal same-symbol rows of available closed
OriginalInput parents in the SAME source. Source Facts, executable guards,
view, input model and ranks stay fixed. The populated caller is not reset.
Incoming Stable, current Good, Contextual, SemanticReady, native Idle,
source growth/history and one current Room remain explicit.
Room uses source node/edge counters, current domains.next and mass 0.
No cache hit/miss, successful run or desired result law is a premise.

The actual execute equation uses the SAME result and full returned state.
Its result is resident and has the canonical conditional contextual EdgeLaw.
The output retains Good, Contextual, SemanticReady, native-machine Extension,
Stable, native Idle, pair-table Extends and Returned.
Ready hits retain the exact checked state. No native Receipt is claimed on
those paths. Native completion is used only by the both-miss branch.
No post-Room, future sequence capacity, reset, model/source rebase,
generated-parent provenance or independent physical language iff follows.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Public Mu unfolding/kept-body, full pass, practical width, solver contracts,
convergence and Haskell refinement remain open. The goal stays incomplete.

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

Preservation covers 84279 starting files/modes. The older non-Audit Lean
count comes from the exact start manifest. All 298 baseline Haskell files,
207 active package files, old proofs, drafts and optimized code remain.
Additional H14 Haskell archives must match baseline source bytes under H14.
Every old document has an exact inverse. The original Audit has 3119
lines and SHA d80480df15a3908dd6c1589b9f6182546d7a4dc09cca9da36098f9289d91c3c6. Its only edit is the new module import.
FINDINGS keeps the external repair index FIRST. PR #65 and PR #97 stay fixed.
No Haskell repair or runtime change is added.

The preceding 1d5a07b7 checkpoint is LOCAL_ONLY. Earlier automatic approval
review rejected pushes. Continuing the goal is not fresh user approval.
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
note = ROOT / 'lean/notes-current-same-symbol-edge-comparison.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
