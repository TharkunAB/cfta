import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb'
SOURCE_LINES = int('257')
assert 0 < SOURCE_LINES <= int('350')
strict, full, audit_stem = 'original-row-group-chain-strict-1', 'original-row-group-chain-public-1', 'original-row-group-chain-audit-1'
metrics = {
    'actual_jobs': int('3'),
    'source_jobs': int('2'),
    'audit_jobs': int('1'),
    'failed_jobs': int('0'),
    'warned_source_exit_zero_jobs': int('0'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3639'),
    'audit_dependencies': int('75499'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == '70787b95484cb69897bc4075858e07c7f9c22433'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentOriginalRowGroupChain.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '936e45b4a31049d6ea43cb1f2bd9756fabef7af92922ff5c0fa294b74442c502'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/original-row-group-chain-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
head_specs = json.loads('[["groups_complete", "7fcdbdb51a0578b4bb359d7ef1648799cbf188cf7bdda79c1ac0d58f7b4b5410", "7fcdbdb51a0578b4bb359d7ef1648799cbf188cf7bdda79c1ac0d58f7b4b5410", "0cbeb28c7e97fe169376f9d14cdcbc10593e3d10edc55eb93e6b48e0c012e601", true, "public-readback/original-row-group-chain-groups_complete-public-type.txt", "public-readback/original-row-group-chain-groups_complete-printed-public-type.txt", "[\\"Classical.choice\\", \\"Quot.sound\\", \\"propext\\"]"]]')
assert [spec[0] for spec in head_specs] == json.loads('["groups_complete"]')
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
    assert head['head'] == 'MicroCFTA.SourceCurrentOriginalRowGroupChain.' + short
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
    assert proof_report['audit_log_sha256'] == 'e203450759dce90167537f93f88e37be32bc0663f062883775e61d1da88164f3'
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == 'e203450759dce90167537f93f88e37be32bc0663f062883775e61d1da88164f3'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} raw checked SHA `{heads[short]['checked_type_sha256']}`; printed {len(printed_types[short])} bytes, SHA `{heads[short]['printed_type_sha256']}`.\n"
    f"{short} raw byte identity: {heads[short]['check_print_type_byte_identity']}; lexical identity: {heads[short]['check_print_type_lexical_identity']}; canonical SHA `{heads[short]['canonical_type_sha256']}`.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Actual original-row symbol-group chain

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-original-row-group-chain.md`.

The selected SourceCurrentOriginalRowGroupChain result derives a finite chain
of actual modeled group runs in the supplied keyed iterator order.
Each run uses its own concrete fuel and the exact preceding full Wrapper.
The source, model, ranked input, width and initial domain cache stay fixed.
The proof retains the genuine current packet and the same global allocation Trace.
One genuine initial Room tuple supports the derived current reserve.
The flattened kept output preserves all-ambient physical union language.
The row view is the literal modeled nodeEdges. Its Mu case is empty and vacuous.
Haskell Mu/union view alignment and generated-parent admission remain open.
No executable outer traversal or HashMap implementation refinement is claimed.
Reconstruction, public Mu/full pass, practical width, solver contracts,
Haskell refinement and convergence remain open. H6 remains strongest combined.
Preservation covers 96320 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
The older12 payload, exact8 through d0cf685f46 and H21 two commits through70787b9548
were pushed and remote-verified. The user authorized further formalize pushes.
The local checkpoint publisher stays LOCAL_ONLY and performs no network command.
Root push follows successful seal and local checkpoint verification.
'''
findings = update
focused = f'''# Actual original-row symbol-group chain

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

The selected reviewed SourceCurrentOriginalRowGroupChain declarations derive
actual H16 group-run equations from H20, once for each supplied iterator entry.
H21 and the old lookup laws identify each reversed bucket with its exact original symbol filter.
The source parent is available, original and closed under the same admitted model.
Each run starts with the preceding full returned Wrapper and an empty kept accumulator.
Each group has a concrete fuel. No common-fuel outer interpreter is claimed.
The proof returns cumulative native Extension, pair-table Extends and Returned retention.
It retains Good, Contextual, SemanticReady, Stable, native Idle and the global Trace.
The source, model, ranks, holds, width, initialDomains and source inventory stay fixed.
The genuine initial Room tuple supports each derived current Room by the same history.
No future Room, reset, width change, comparison-completion callback or success premise is added.
The flattened output retains original membership, its length bound and all-ambient physical union iff.
Outer iterator order stays supplied. Final heaps need not agree across different orders.
The literal modeled nodeEdges gives ordinary stored rows and an empty Mu case.
That vacuous Mu case does not prove Haskell Mu/union unfolding behavior.
Generated parents after child reconstruction still need admission and rebase.
Actual outer traversal refinement, reconstruction, public Mu/full pass, practical width,
solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains strongest combined. The whole goal is incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Default declaration limits and all linters remain.
The source hard stop is {int('350')} lines. Diagnostics follow the complete module.
FULL retains {len(raw)} raw bytes. Complete check/print TYPEs agree after ASCII whitespace normalization.
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
Retained evidence records every actual source and metadata outcome.
Metadata work creates no proof command. Audit has {metrics['audit_build_jobs']}
jobs and {metrics['audit_dependencies']} theorem dependencies.
This writer claims no seal or local publication success.

Preservation covers 96320 files/modes and 3637 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, proofs, drafts,
counterexamples and optimized code remain. Extra H22 Haskell archives must
match baseline source bytes. Nine document inverses preserve all old text.
The original Audit has 3127 lines and SHA 4c54e8f578cc9e12084e7306671e6c6410150811a3868fc128b90805ae5452e1.
Its sole edit is the new module import. FINDINGS retains the repair index FIRST.
PR #65 and PR #97 remain fixed. No Haskell repair or runtime change is added.

The older12 payload was pushed and verified at562120d456.
The exact8 through d0cf685f46 and H21 two commits through70787b9548 were pushed and remote-verified.
The user authorized further pushes to formalize. H22 seal and push are not claimed here.
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
note = ROOT / 'lean/notes-current-original-row-group-chain.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
