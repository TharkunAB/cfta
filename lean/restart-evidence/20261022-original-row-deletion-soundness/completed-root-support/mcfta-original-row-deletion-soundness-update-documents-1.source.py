import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = 'a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a'
SOURCE_LINES = int('105')
assert 0 < SOURCE_LINES <= 180
strict, full, audit_stem = 'original-row-deletion-soundness-strict-1', 'original-row-deletion-soundness-public-1', 'original-row-deletion-soundness-audit-1'
metrics = {
    'actual_jobs': int('3'),
    'source_jobs': int('2'),
    'audit_jobs': int('1'),
    'failed_jobs': int('0'),
    'warned_source_exit_zero_jobs': int('0'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3636'),
    'audit_dependencies': int('75454'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == 'a8223aafa4ef99da5570f2013aadc14af99076b3'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentOriginalRowDeletionSoundness.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'b754194bf85bd6c73e6dae7eef38f0563fa43e69c2b5aff5317e5a859f4c3457'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/original-row-deletion-soundness-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
head_specs = [
    ('deletion_sound', 'b83d40149dd1db19b919413d5eca5a5177e0f99fec652f800444a61f535462b5', 'public-readback/original-row-deletion-soundness-deletion_sound-public-type.txt', 'public-readback/original-row-deletion-soundness-deletion_sound-printed-public-type.txt', '["Classical.choice", "Quot.sound", "propext"]'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentOriginalRowDeletionSoundness.' + short
    assert head['check_print_type_identity'] and head['check_print_type_byte_identity'] and head['unique_complete_type_body_delimiter']
    checked = (HERE / type_path).read_bytes()
    assert checked == (HERE / printed_path).read_bytes() and hashlib.sha256(checked).hexdigest() == type_sha
    assert not any(marker in checked.decode() for marker in ['_private', '✝', '†', '‡']) and head['private_public_type_names'] is False
    assert head['actual_axioms'] == json.loads(axioms_json)
    assert head['actual_axioms_within_standard_allowed'] and set(head['actual_axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
    checked_types[short] = checked
for mode, expected_live in [('normal', False), ('live', True)]:
    proof_report = json.loads((HERE / ('proof-evidence-' + mode + '.json')).read_text())
    assert proof_report['status'] == 'PASS' and proof_report['live'] is expected_live
    assert all(proof_report[key] == value for key, value in metrics.items())
    assert proof_report['audit_log_sha256'] == 'da1e97ab1910308be353811d334d4f294181e7f7ab8f0f7567716fd6231f0616'
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == 'da1e97ab1910308be353811d334d4f294181e7f7ab8f0f7567716fd6231f0616'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Soundness of identity-based original-row deletion

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-original-row-deletion-soundness.md`.

SourceCurrentOriginalRowDeletionSoundness.deletion_sound is a pure completed-result adapter.
It keeps one source, arbitrary holds, an admitted input model and its fixed ranked index.
Both operands are literal rows of one original available closed parent.
The SAME H15 result's canonical empty-domain EdgeLaw is an explicit premise.
Result residency, source-to-final growth and final heap coherence remain explicit.
Candidate identity gives candidate language included in pivot language.
Pivot identity gives the converse, for every ambient environment.
Canonical ordering swaps only the semantic conjunction. Candidate-first control stays fixed.

H18 supplies the original/admitted child and physical row-meaning bridge.
This adapter adds no comparison execution, scan invariant or physical pruning theorem.
Future cluster semantics retains H17's genuine width, global Room and full current packet.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Grouping, generated parents, public Mu/full pass, practical width, solver contracts,
Haskell refinement and convergence remain open. The whole goal is incomplete.

Preservation covers 90717 baseline files/modes, 298 baseline Haskell files
and 207 active package files. Only one Audit import and nine additive doc
prefixes may change old files. FINDINGS keeps its repair index FIRST.
The retained local payload through 562120d456 remains LOCAL_ONLY.
Remote publication is PENDING_USER_APPROVAL. This tool performs no network command.
'''
findings = update
focused = f'''# Soundness of identity-based original-row deletion

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

deletion_sound derives two language inclusions from a completed comparison result.
Source Facts, arbitrary holds, the admitted input model and its RankedInput index stay fixed.
The parent is original, available and closed. Both operands are literal rows of that parent.
Parent admission in the same model remains explicit.
The full canonical empty-domain EdgeLaw is an explicit argument with sound and complete fields.
At the scan call site, this law belongs to the SAME existing H15 witness.
The actual common edge is resident in the final coherent heap, which extends the source.

H18 supplies child Original/admission and physical row meanings for every ambient environment.
The derivation uses EdgeLaw.sound and the empty-domain sound-context law.
The fixed ranked index remains in the existing EdgeLaw type. Its bounded completeness projection and rank erasure are not used.
Source row residency and heap growth place both operands in that same final heap.
Edge identity uniqueness derives whole payload equality from either tested identity equality.
Common=candidate implies candidate language included in pivot language.
Common=pivot implies pivot language included in candidate language.
Both implications apply for every ambient environment.
The second implication needs no failed-first-test premise. Actual control remains candidate-first.
Canonical ordering swaps conjunction components only. No execution symmetry is inferred.

This adapter executes no comparison and produces no resource packet.
Its completed-result premises are supplied by the SAME H15 witness at the later call site.
Every other current packet field must remain available to that scan proof.
No NEW completeness, total-meet or desired-inclusion oracle is introduced.
The later cluster semantic theorem retains genuine H17 width, global Room and the full current packet.
It adds no future-success or post-Room oracle. Parent admission cannot be inferred from H17 membership alone.
The scan union-language invariant and physical pruning theorem remain open.
Grouping, reconstruction, generated parents, public Mu unfolding/kept-body, the full public pass,
practical width, solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem. The whole goal is incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Declaration limits remain unchanged.
The source has a hard180-line limit. All strict linters remain enabled.
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

Preservation covers 90717 starting files/modes and 3634 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, old proofs,
drafts, counterexamples and optimized code remain.
Additional H19 Haskell archives must match baseline source bytes under H19.
Every old document has an exact inverse. The original Audit has 3124
lines and SHA 3dcbcdcec1ff02d14f17784dda3eba709811d291e1c82619d5eb1b4fac4ecd4e.
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
note = ROOT / 'lean/notes-current-original-row-deletion-soundness.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
