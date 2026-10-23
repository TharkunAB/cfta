import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '09e8927b6e9a98fa39704567fd6b48164dfc2a30d45ea389e0d8e4a36d71116b'
SOURCE_LINES = int('152')
assert 0 < SOURCE_LINES <= int('180')
strict, full, audit_stem = 'both-miss-native-covered-strict-1', 'both-miss-native-covered-public-1', 'both-miss-native-covered-audit-1'
metrics = {
    'actual_jobs': int('3'),
    'source_jobs': int('2'),
    'audit_jobs': int('1'),
    'failed_jobs': int('0'),
    'warned_source_exit_zero_jobs': int('0'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3643'),
    'audit_dependencies': int('75504'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '6ca7ff763c6e18d69904b4e860c11f7959eb3d13'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeOriginalRowsCovered.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'e7b8013f2f8e898ca6177cafb96ce48bc8ffeafee3e6f9e66ec02e2f112ae4d0'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/both-miss-native-covered-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
head_specs = json.loads('[["both_miss_complete", "8db732881105e579a8efc96244810eaea5d33473095023fb6445347c63082903", "8db732881105e579a8efc96244810eaea5d33473095023fb6445347c63082903", "cac79dbfe33ad7bda188e468abe471b11c0ae05d9653436bdfd0772a46276081", true, "public-readback/both-miss-native-covered-both_miss_complete-public-type.txt", "public-readback/both-miss-native-covered-both_miss_complete-printed-public-type.txt", "[\\"Classical.choice\\", \\"Quot.sound\\", \\"propext\\"]"]]')
assert [spec[0] for spec in head_specs] == json.loads('["both_miss_complete"]')
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
    assert head['head'] == 'MicroCFTA.SourceCurrentSameSymbolEdgeOriginalRowsCovered.' + short
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
    assert proof_report['audit_log_sha256'] == '8f408f71d6d34a931a73666491b71fe7ba54f53384dd99b75a37027312315c95'
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == '8f408f71d6d34a931a73666491b71fe7ba54f53384dd99b75a37027312315c95'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} raw checked SHA `{heads[short]['checked_type_sha256']}`; printed {len(printed_types[short])} bytes, SHA `{heads[short]['printed_type_sha256']}`.\n"
    f"{short} raw byte identity: {heads[short]['check_print_type_byte_identity']}; lexical identity: {heads[short]['check_print_type_lexical_identity']}; canonical SHA `{heads[short]['canonical_type_sha256']}`.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Native coverage through one original-row comparison

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-both-miss-native-covered.md`.

The checked theorem augments the SAME H13 BOTH-miss comparison with final native Covered.
It specializes the fixed model and ranks to finiteInputMeaning and finiteRankedInput.
Genuine parent model admission and incoming native Covered remain explicit.
One H13 invocation supplies the actual result, full after state and native Receipt.
The proof keeps every H13 output and uses that SAME Receipt.trace for coverage.
Actual branch admission and the literal edgeBody certificate feed Trace.covered.
No pair-admission output, generated-root composition, new resources, Mu/full pass,
practical-width claim, Haskell refinement or convergence is derived.
H6 constructed_node_calls remains strongest combined. The whole goal is incomplete.
Preservation covers 102314 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
H25 was pushed and remote-verified at6ca7ff763c6e18d69904b4e860c11f7959eb3d13.
The user authorized further pushes to formalize. H26 seal and push remain future work.
The local publisher stays LOCAL_ONLY and has no network command.
Root push follows successful seal and local checkpoint verification.
'''
findings = update
focused = f'''# Native coverage through one original-row comparison

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

The checked theorem invokes H13 BOTH-miss completion exactly once.
It keeps the SAME actual result, Wrapper after state and native Receipt.trace.
Every H13 output remains, including final Stable, native Idle and the memo tuple.
The source, holds, finite input meaning and finite ranked input stay fixed.
Genuine parent model admission and initial native Covered are explicit premises.
Public row admission, residency, growth and empty-domain scope/readiness facts
supply the actual derived branches and literal edgeBody certificate.
Trace.covered derives native Covered at the SAME completed native trace endpoint.
The proof does not replace that witness with a second execution or an assumed final certificate.
No pair-admission output, generated-root composition, new resource packet,
Mu/full pass, practical width, solver correspondence, Haskell refinement
or convergence is derived. Ready hits have no native Receipt.
H6 constructed_node_calls remains strongest combined. The whole goal is incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Default declaration limits and all linters remain.
The source hard stop is {int('180')} lines. Diagnostic options follow the complete module.
FULL retains {len(raw)} raw bytes. Complete TYPEs agree under four-character ASCII whitespace normalization.
{type_summary}
Root and an independent reviewer read each complete checked public TYPE.
Both raw TYPE views remain. Per-head byte identity is reported above.
No second manual TYPE read or whole-body manual read is claimed.
All four private markers are absent from TYPE. The prospective module permits no private helpers.
Whole bodies remain retained and checked programmatically.
Actual per-declaration axioms are recorded. Empty sets and standard subsets are permitted.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failures, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. All actual inputs, raw logs and repair history remain.
Metadata work creates no proof command. Audit has {metrics['audit_build_jobs']}
build jobs and {metrics['audit_dependencies']} theorem dependencies.
This writer claims no seal or local publication success.

Preservation covers 102314 files/modes and 3641 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, proofs, drafts,
counterexamples and optimized code remain. Extra H26 Haskell archives must match baseline bytes.
Nine document inverses preserve all old text.
The original Audit has 3131 lines and SHA b616bb97d542e1494bfbef2d6c3c77365c28731ff8a8a612e59533b44bc783e3.
Its sole edit is the new module import. FINDINGS retains the repair index FIRST.
PR #65 and PR #97 remain fixed. No Haskell repair or runtime change is added.

H25 was pushed and remote-verified at6ca7ff763c6e18d69904b4e860c11f7959eb3d13.
The standing user authorization permits further pushes to formalize.
H26 seal and push are not claimed here.
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
note = ROOT / 'lean/notes-current-both-miss-native-covered.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
