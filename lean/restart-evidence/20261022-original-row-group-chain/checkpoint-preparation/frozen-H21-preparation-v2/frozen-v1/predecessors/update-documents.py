import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = 'e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8'
SOURCE_LINES = int('393')
assert 0 < SOURCE_LINES <= 500
strict, full, audit_stem = 'original-row-cluster-language-strict-2', 'original-row-cluster-language-public-1', 'original-row-cluster-language-audit-1'
metrics = {
    'actual_jobs': int('4'),
    'source_jobs': int('3'),
    'audit_jobs': int('1'),
    'failed_jobs': int('0'),
    'warned_source_exit_zero_jobs': int('1'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3637'),
    'audit_dependencies': int('75482'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '21dbf7da7ec880f6d9673213934f764e6fda7999'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentOriginalRowClusterLanguage.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'b63da6894e9f7d794c8ecaa1bee4bb76664d556d8d96cd2ab0fef8bd060fb34f'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/original-row-cluster-language-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
assert readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == 1
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
head_specs = [
    ('cluster_complete', 'c389a111047d46708592ebc6c0b098106bcd6121f25b490285d4f6e0cf3f9f4c', 'public-readback/original-row-cluster-language-cluster_complete-public-type.txt', 'public-readback/original-row-cluster-language-cluster_complete-printed-public-type.txt', '["Classical.choice", "Quot.sound", "propext"]'),
]
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types = {}
for short, type_sha, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentOriginalRowClusterLanguage.' + short
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
    assert proof_report['audit_log_sha256'] == '9dee6d0995dd5b2b6a7e3ea9dc5866df756abe877e590d15c96fb23a50c597ea'
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '9dee6d0995dd5b2b6a7e3ea9dc5866df756abe877e590d15c96fb23a50c597ea'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Physical language preservation for one original symbol group

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-original-row-cluster-language.md`.

SourceCurrentOriginalRowClusterLanguage.cluster_complete constructs the modeled scan run
and preserves the physical union language of its exact original symbol group.
For every ambient environment and term, some kept row accepts the term iff
some original filtered row accepts it. All H17 current-packet outputs remain.
Source facts, holds, the admitted input model and ranked index stay fixed.
The parent is original, available and closed. Width, initial-domain Valid,
global allocation Trace and genuine global Room remain explicit.
The proof uses the SAME H15 result and H19 deletion implications at each comparison.
It preserves the populated caller, candidate-first branch order and native history.
The modeled control is noncomputable. No second comparison or meet oracle is added.

Grouping, reconstruction, generated parents, public Mu/full pass, practical width,
solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Preservation covers 91951 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
The directly approved 12-commit payload was pushed and its remote tip verified at 562120d456.
Newer local work needs fresh exact-payload approval. This checkpoint stays LOCAL_ONLY.
Network publication is PENDING_USER_APPROVAL. This tool performs no network command.
'''
findings = update
focused = f'''# Physical language preservation for one original symbol group

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

cluster_complete constructs the actual modeled H16 scan from .cluster rows [].
Its kept rows preserve the physical union language of the exact symbol-filtered rows.
The iff holds for every ambient environment and finite term with the same holds.
Original-row membership, length bounds and all H17 current-packet outputs remain.
The parent stays original, available and closed. Admission in the same model is explicit.
Source Facts, formulas, solver, InputMeaning and its RankedInput index stay fixed.
One genuine mathematical width and global Room remain explicit.
The same initial-domain Valid and allocation Trace continue through every comparison.
Final global Trace permits the next current Room derivation. No future Room oracle is added.

The proof strengthens H17's concrete induction in a new module.
It retains the SAME actual common result, final state, residency and canonical EdgeLaw from H15.
H19 derives the two inclusions from that full EdgeLaw argument using its sound projection.
The existing law contains sound and complete fields. The bounded-completeness projection is not used for deletion.
There is no rank erasure, replacement model, second comparison or exact-meet oracle.
Candidate deletion uses candidate included in pivot. Promotion uses pivot included in candidate.
The remaining branch and both reversals use list membership. No semantic incomparability is claimed.
The modeled control is noncomputable. This is not a compiled Haskell execution claim.

Grouping all symbols, reconstruction, generated parents, public Mu unfolding/kept-body,
the full public pass, practical width, solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem. The whole goal is incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Declaration limits remain unchanged.
The source has a hard500-line limit. All strict linters remain enabled.
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

Preservation covers 91951 starting files/modes and 3635 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, old proofs,
drafts, counterexamples and optimized code remain.
Additional H20 Haskell archives must match baseline source bytes under H20.
Every old document has an exact inverse. The original Audit has 3125
lines and SHA 7e754f81ab43baeace185b866adaf0a38c61ab347b402752cf83bba73882de5e.
Its only edit is the new module import.
FINDINGS keeps the external repair index FIRST. PR #65 and PR #97 stay fixed.
No Haskell repair or runtime change is added.

The directly approved 12-commit payload was pushed and its remote tip verified at 562120d456.
That approval does not cover newer local work. A future payload needs fresh exact approval.
Earlier pending-12 notes remain historical. This checkpoint remains LOCAL_ONLY.
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
note = ROOT / 'lean/notes-current-original-row-cluster-language.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
