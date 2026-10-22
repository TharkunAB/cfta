import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435'
SOURCE_LINES = int('210')
assert 0 < SOURCE_LINES <= int('350')
strict, full, audit_stem = 'original-row-reconstruction-strict-2', 'original-row-reconstruction-public-1', 'original-row-reconstruction-audit-1'
metrics = {
    'actual_jobs': int('4'),
    'source_jobs': int('3'),
    'audit_jobs': int('1'),
    'failed_jobs': int('1'),
    'warned_source_exit_zero_jobs': int('0'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3640'),
    'audit_dependencies': int('75501'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '87c0eabce252c0017b1c060750c0a06ebd4fe9b3'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentOriginalRowReconstruction.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '6b234343f2185f8a9c889ef4c165d8298024155a30b40da0e9f83336080a94a3'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/original-row-reconstruction-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
head_specs = json.loads('[["ordinary_complete", "41b97f6d0dc108847e84ef67e0011a880bc222ec1849513161649bb2a031e5bb", "41b97f6d0dc108847e84ef67e0011a880bc222ec1849513161649bb2a031e5bb", "abb88869af3c129d9d5df7e8b056a9ad52d6d59fdef91e75c6610f2bfcbd7b1d", true, "public-readback/original-row-reconstruction-ordinary_complete-public-type.txt", "public-readback/original-row-reconstruction-ordinary_complete-printed-public-type.txt", "[\\"Classical.choice\\", \\"Quot.sound\\", \\"propext\\"]"]]')
assert [spec[0] for spec in head_specs] == json.loads('["ordinary_complete"]')
assert head_specs and readback['owned_public_job_exit'] == 0 and readback['no_omissions'] and len(readback['heads']) == len(head_specs)
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['complete_public_type_root_review'] == review['independent_complete_public_type_review'] == 'CLEAR'
assert review['root_printed_type_lexical_identity_verified'] is True
normalize = lambda text: re.sub(r'[ \t\r\n]+', ' ', text).strip(' \t\r\n')
heads = {head['head'].rsplit('.', 1)[1]: head for head in readback['heads']}
assert set(heads) == {spec[0] for spec in head_specs}
checked_types, printed_types = {}, {}
for short, type_sha, printed_sha, canonical_sha, raw_identity, type_path, printed_path, axioms_json in head_specs:
    head = heads[short]
    assert head['head'] == 'MicroCFTA.SourceCurrentOriginalRowReconstruction.' + short
    assert head['check_print_type_identity'] and head['check_print_type_lexical_identity'] and head['unique_complete_type_body_delimiter']
    checked = (HERE / type_path).read_bytes()
    printed = (HERE / printed_path).read_bytes()
    assert hashlib.sha256(checked).hexdigest() == type_sha == head['checked_type_sha256'] and len(checked) == head['checked_type_bytes']
    assert hashlib.sha256(printed).hexdigest() == printed_sha == head['printed_type_sha256'] and len(printed) == head['printed_type_bytes']
    assert normalize(checked.decode()) == normalize(printed.decode()) and hashlib.sha256(normalize(checked.decode()).encode()).hexdigest() == canonical_sha == head['canonical_type_sha256']
    assert type(raw_identity) is bool and raw_identity == (checked == printed) and head['check_print_type_byte_identity'] is raw_identity
    assert review['raw_type_byte_identity_by_head'][short] is raw_identity
    assert not any(marker in checked.decode() for marker in ['_private', '✝', '†', '‡']) and head['private_public_type_names'] is False
    assert head['actual_axioms'] == json.loads(axioms_json)
    assert head['actual_axioms_within_standard_allowed'] and set(head['actual_axioms']) <= {'Classical.choice', 'Quot.sound', 'propext'}
    checked_types[short], printed_types[short] = checked, printed
for mode, expected_live in [('normal', False), ('live', True)]:
    proof_report = json.loads((HERE / ('proof-evidence-' + mode + '.json')).read_text())
    assert proof_report['status'] == 'PASS' and proof_report['live'] is expected_live
    assert all(proof_report[key] == value for key, value in metrics.items())
    assert proof_report['audit_log_sha256'] == 'f97a5d4ff4987b5276453d67d2c9560aea9de81b315a2a9510ea4165fafa32c9'
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == 'f97a5d4ff4987b5276453d67d2c9560aea9de81b315a2a9510ea4165fafa32c9'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} raw checked SHA `{heads[short]['checked_type_sha256']}`; printed {len(printed_types[short])} bytes, SHA `{heads[short]['printed_type_sha256']}`.\n"
    f"{short} raw byte identity: {heads[short]['check_print_type_byte_identity']}; lexical identity: {heads[short]['check_print_type_lexical_identity']}; canonical SHA `{heads[short]['canonical_type_sha256']}`.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Ordinary original-row reconstruction

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-original-row-reconstruction.md`.

The checked theorem uses one ordinary original parent in the fixed admitted model.
It retains the H22 group equations and their exact final populated caller.
It then runs the existing raw makeNode work at that same returned heap.
The result is available, ordinary and closed, with physical language iff
for every ambient environment. The exact current packet and global Trace remain.
This raw natural-index constructor path adds no fresh-result width safety,
new-source Room, generated-root admission or model/rank rebase.
It does not prove an all-group interpreter, generated-parent traversal,
Mu/full-pass behavior, Haskell refinement, practical width or convergence.
H6 constructed_node_calls remains strongest combined. The whole goal remains active.
Preservation covers 98415 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
H22 was pushed and remote-verified at87c0eabce252c0017b1c060750c0a06ebd4fe9b3.
The user authorized further pushes to formalize. H23 seal and push remain future work.
The local publisher stays LOCAL_ONLY and has no network command.
Root push follows successful seal and local checkpoint verification.
'''
findings = update
focused = f'''# Ordinary original-row reconstruction

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

The checked result derives the H22 group chain once from its genuine packet.
It keeps the same source, admitted input model, ranked input, holds, width
and initial domain cache. The parent is an actual original available closed ordinary node.
It selects H22's exact final full Wrapper and flattened kept rows.
The existing native work instruction runs makeNode on that heap.
The following pure instruction completes the checked-demand execution with fuel two.
The raw reconstruction retains both native memo tables, operation caches, domains and pair memo.
The result is available, ordinary and closed. It can normalize to empty.
It has the original parent's physical language for every ambient environment.
The proof retains Good, Contextual, SemanticReady, Stable, native Idle,
source growth, issued history and the same global allocation Trace.
It composes native Extension, pair-table Extends and Returned retention.
Public source-child free-name facts justify closedness. No private H18 helper is exported.
The model and contextual laws stay fixed while actual residency moves through heap growth.
The old initial-source Room remains the same arithmetic proposition.
Raw work does not establish new allocated-word admission or fresh-result key safety.
The fixed old input model does not admit the rebuilt root automatically. Populated-cache rebase, new-source Room and fresh-key safety remain open.
No result identity or unnormalized stored-row equality is claimed.
All-group execution, generated-parent traversal, Mu/full pass, practical width,
solver correspondence, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains strongest combined. The whole goal is incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Default declaration limits and all linters remain.
The source hard stop is {int('350')} lines. Diagnostic options follow the complete module.
FULL retains {len(raw)} raw bytes. Complete TYPEs agree under four-character ASCII whitespace normalization.
{type_summary}
Root and an independent reviewer read each complete checked public TYPE.
Both raw TYPE views remain. Per-head byte identity is reported above.
No second manual TYPE read or whole-body manual read is claimed.
All four private markers and recorded helper names are absent from TYPE.
Whole bodies remain retained and checked programmatically.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failures, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. All actual inputs, raw logs and repair history remain.
Metadata work creates no proof command. Audit has {metrics['audit_build_jobs']}
build jobs and {metrics['audit_dependencies']} theorem dependencies.
This writer claims no seal or local publication success.

Preservation covers 98415 files/modes and 3638 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, proofs, drafts,
counterexamples and optimized code remain. Extra H23 Haskell archives must match baseline bytes.
Nine document inverses preserve all old text.
The original Audit has 3128 lines and SHA ebcc4770268c142e8fb5370dadcbf9be224276f4c7b0240c9876df55444715de.
Its sole edit is the new module import. FINDINGS retains the repair index FIRST.
PR #65 and PR #97 remain fixed. No Haskell repair or runtime change is added.

H22 was pushed and remote-verified at87c0eabce252c0017b1c060750c0a06ebd4fe9b3.
The standing user authorization permits further pushes to formalize.
H23 seal and push are not claimed here.
The local publisher stays LOCAL_ONLY/AUTHORIZED_PENDING_ROOT_PUSH.
It retains seal, scoped staging and filesystem/index/HEAD checks and runs no network command.
Root push follows successful seal and local checkpoint verification.
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
note = ROOT / 'lean/notes-current-original-row-reconstruction.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
