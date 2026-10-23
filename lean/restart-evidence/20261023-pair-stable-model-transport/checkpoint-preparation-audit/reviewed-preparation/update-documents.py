import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '__H24_SOURCE_SHA__'
SOURCE_LINES = int('__H24_SOURCE_LINES__')
assert 0 < SOURCE_LINES <= int('__H24_SOURCE_HARD_STOP__')
strict, full, audit_stem = '__H24_SELECTED_STRICT_STEM__', '__H24_SELECTED_FULL_STEM__', '__H24_AUDIT_STEM__'
metrics = {
    'actual_jobs': int('__H24_ACTUAL_JOBS__'),
    'source_jobs': int('__H24_SOURCE_JOBS__'),
    'audit_jobs': int('__H24_AUDIT_JOBS__'),
    'failed_jobs': int('__H24_FAILED_JOBS__'),
    'warned_source_exit_zero_jobs': int('__H24_WARNED_SOURCE_EXIT_ZERO_JOBS__'),
    'rejected_public_type_jobs': int('__H24_REJECTED_PUBLIC_TYPE_JOBS__'),
    'audit_build_jobs': int('__H24_AUDIT_BUILD_JOBS__'),
    'audit_dependencies': int('__H24_AUDIT_DEPENDENCIES__'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '0d03a28e82f9f3d0b5dfbba16bc919fb16c422cb'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/__H24_MODULE_NAME__.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '__H24_FULL_RAW_SHA__'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/pair-stable-model-transport-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
head_specs = json.loads('__H24_HEAD_SPECS_JSON__')
assert [spec[0] for spec in head_specs] == json.loads('__H24_PUBLIC_HEAD_NAMES_JSON__')
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
    assert head['head'] == 'MicroCFTA.__H24_MODULE_NAME__.' + short
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
    assert proof_report['audit_log_sha256'] == '__H24_AUDIT_SHA__'
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '__H24_AUDIT_SHA__'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} raw checked SHA `{heads[short]['checked_type_sha256']}`; printed {len(printed_types[short])} bytes, SHA `{heads[short]['printed_type_sha256']}`.\n"
    f"{short} raw byte identity: {heads[short]['check_print_type_byte_identity']}; lexical identity: {heads[short]['check_print_type_lexical_identity']}; canonical SHA `{heads[short]['canonical_type_sha256']}`.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Stable pair model transport

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-pair-stable-model-transport.md`.

The checked theorem transports Stable for the same populated Wrapper.
It requires finite input agreement and genuine old captured canonical request admission.
It transports both EdgeLaw fields and the ranked input index. It keeps the complete state.
It does not produce actual admission, native Covered, new-source Room or WordRanges.
Generated-node composition, Mu/full pass, practical width, Haskell refinement
and convergence remain open. H6 constructed_node_calls remains strongest combined.
Preservation covers 100056 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
H23 was pushed and remote-verified at0d03a28e82f9f3d0b5dfbba16bc919fb16c422cb.
The user authorized further pushes to formalize. H24 seal and push remain future work.
The local publisher stays LOCAL_ONLY and has no network command.
Root push follows successful seal and local checkpoint verification.
'''
findings = update
focused = f'''# Stable pair model transport

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

The checked theorem transports Stable on the same populated Wrapper.
Finite input agreement and admission of the actual old captured canonical requests
are explicit premises. They are not produced by this theorem.
The proof transports both soundness and bounded completeness in EdgeLaw.
The model and ranked index can change under the explicit agreement premises.
The checked state, pair memo, keys, statuses, captures and results stay the same.
No execution, allocation or native Receipt is produced by this pure transport.
No actual admission producer or new-node composition is derived.
Native Covered, new-source Room, WordRanges, Mu/full pass, practical width,
solver correspondence, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains strongest combined. The whole goal is incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Default declaration limits and all linters remain.
The source hard stop is {int('__H24_SOURCE_HARD_STOP__')} lines. Diagnostic options follow the complete module.
FULL retains {len(raw)} raw bytes. Complete TYPEs agree under four-character ASCII whitespace normalization.
{type_summary}
Root and an independent reviewer read each complete checked public TYPE.
Both raw TYPE views remain. Per-head byte identity is reported above.
No second manual TYPE read or whole-body manual read is claimed.
All four private markers are absent from TYPE. The module permits no private helpers.
Whole bodies remain retained and checked programmatically.
Actual per-declaration axioms are recorded. Empty sets and standard subsets are permitted.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failures, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. All actual inputs, raw logs and repair history remain.
Metadata work creates no proof command. Audit has {metrics['audit_build_jobs']}
build jobs and {metrics['audit_dependencies']} theorem dependencies.
The first bootstrap pull timed out over SSH22. Its verified terminal result and
successful one-command HTTPS retry remain archived. These are not proof jobs.
This writer claims no seal or local publication success.

Preservation covers 100056 files/modes and 3639 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, proofs, drafts,
counterexamples and optimized code remain. Extra H24 Haskell archives must match baseline bytes.
Nine document inverses preserve all old text.
The original Audit has 3129 lines and SHA f3f370610be0dddc7b2f21b77af15f21cc11774a95b8ecf93cd63748b6ed9145.
Its sole edit is the new module import. FINDINGS retains the repair index FIRST.
PR #65 and PR #97 remain fixed. No Haskell repair or runtime change is added.

H23 was pushed and remote-verified at0d03a28e82f9f3d0b5dfbba16bc919fb16c422cb.
The standing user authorization permits further pushes to formalize.
H24 seal and push are not claimed here.
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
note = ROOT / 'lean/notes-current-pair-stable-model-transport.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
