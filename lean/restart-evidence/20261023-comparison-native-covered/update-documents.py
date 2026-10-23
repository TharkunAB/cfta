import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = 'c923d6ffba1ccd787aa7384225e34232b5ff3b6098be671355787b982ead3f01'
SOURCE_LINES = int('204')
assert 0 < SOURCE_LINES <= int('230')
strict, full, audit_stem = 'comparison-native-covered-strict-1', 'comparison-native-covered-public-1', 'comparison-native-covered-audit-1'
metrics = {
    'actual_jobs': int('3'),
    'source_jobs': int('2'),
    'audit_jobs': int('1'),
    'failed_jobs': int('0'),
    'warned_source_exit_zero_jobs': int('0'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3645'),
    'audit_dependencies': int('75508'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == 'b796e8e660a73ac328d41cad53c61099ba79d93f'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeComparisonCovered.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '01e903addd01f1d88413664ef8eed2664b1236e61387879d22c4c58755d0887e'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/comparison-native-covered-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
head_specs = json.loads('[["original_rows_complete", "73f30229b7c09cdbfa0ebee0a99d161f66b32089d51e4b6be79bd9a7aeeab485", "73f30229b7c09cdbfa0ebee0a99d161f66b32089d51e4b6be79bd9a7aeeab485", "a253d2cbaec020446702878a811dd890ff1e14eb93a121bef05f24d302327fb1", true, "public-readback/comparison-native-covered-original_rows_complete-public-type.txt", "public-readback/comparison-native-covered-original_rows_complete-printed-public-type.txt", "[\\"Classical.choice\\", \\"Quot.sound\\", \\"propext\\"]"]]')
assert [spec[0] for spec in head_specs] == json.loads('["original_rows_complete"]')
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
    assert head['head'] == 'MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered.' + short
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
    assert proof_report['audit_log_sha256'] == 'cc3983fd3d75f7c2120d3e8614c174598a9828fb691623d1dddd0433d12686ae'
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == 'cc3983fd3d75f7c2120d3e8614c174598a9828fb691623d1dddd0433d12686ae'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} raw checked SHA `{heads[short]['checked_type_sha256']}`; printed {len(printed_types[short])} bytes, SHA `{heads[short]['printed_type_sha256']}`.\n"
    f"{short} raw byte identity: {heads[short]['check_print_type_byte_identity']}; lexical identity: {heads[short]['check_print_type_lexical_identity']}; canonical SHA `{heads[short]['canonical_type_sha256']}`.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## {json.loads('"Native coverage through original-row comparisons"')}

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-comparison-native-covered.md`.

{json.loads('"The checked theorem adds native Covered to the SAME H15 comparison result and full caller.\\nOne finite inventory fixes the source view, model, ranks and guard semantics.\\nGenuine admission of both closed original parents and incoming native Covered remain premises.\\nThe arbitrary initial domain cache, Valid, global allocation Trace and initial Room remain explicit.\\nOne H15 invocation supplies the exact fuel, result, after state and all twelve existing outputs.\\nH27 handles either cache hit through checked-state equality from that SAME done equation.\\nOn a miss, public raw-step readback and prefix admission derive the physical Trace at those endpoints.\\nActual row admission and public branch certificates then derive final native Covered.\\nPair admission through group runs, generated-root composition, new resources, Mu/full pass, practical width,\\nHaskell refinement and convergence remain open."')}
H6 constructed_node_calls remains strongest combined.
The whole goal remains ACTIVE and incomplete.
Preservation covers 106098 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
H27 was pushed and remote-verified at b796e8e660a73ac328d41cad53c61099ba79d93f.
The user authorized further pushes to formalize. H28 seal and push remain future work.
The local publisher stays LOCAL_ONLY and has no network command.
Root push follows successful seal and local checkpoint verification.
'''
findings = update
focused = f'''# {json.loads('"Native coverage through original-row comparisons"')}

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

{json.loads('"SourceCurrentSameSymbolEdgeComparisonCovered.original_rows_complete completes one original-row comparison.\\nIt fixes one source, finite inventory, finiteInputMeaning, finiteRankedInput and guard semantics.\\nBoth parents are original, available, closed and admitted. Both rows are literal members with the same symbol.\\nThe populated Wrapper retains its Stable, Good, Contextual, SemanticReady and native Idle premises.\\nIncoming native Covered, source growth and issued history remain explicit.\\nThe proof retains the same initialDomains parameter and its Valid proof.\\nThe SAME global allocation Trace and one genuine initial Room support the comparison at fixed width.\\nOne H15 invocation supplies the exact fuel, result, full after and done equation.\\nAll twelve H15 outputs remain. The only additional output is native Covered at that same after state.\\nA published-key hit uses H27 on the SAME done equation to derive checked-state equality.\\nA miss uses public miss_readback on the SAME done equation to recover raw native Steps.\\nActual parent admission and literal row residency derive request scope and coverage.\\nCanonical ordering swaps complete Edge records and both scope and admission facts together.\\nOnly the literal emptyDomain request has no binding obligations. Source bindings can be nonempty.\\nThe initial packet supplies Resources and Current. Public prefix admission derives a physical Receipt\\nat the exact before.checked and after.checked endpoints. Its trace feeds Trace.covered.\\nPublic branch certificates and the derived local admission certificate supply final native Covered.\\nThe proof selects no second comparison or hidden H15 receipt. It uses no helper or induction.\\nCaptured-pair Requests and canonical returned-pair admission remain separate.\\nComposition with generated-root source/model/rank transport, deriving new fixed-width Room\\nand WordRanges, literal Mu/full pass,\\npractical width, Haskell and solver correspondence, and convergence remain open."')}
H6 constructed_node_calls remains strongest combined.
The whole goal remains ACTIVE and incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Default declaration limits and all linters remain.
The source hard stop is {int('230')} lines. Diagnostic options follow the complete module.
FULL retains {len(raw)} raw bytes. Complete TYPEs agree under four-character ASCII whitespace normalization.
{type_summary}
Root and an independent reviewer read each complete checked public TYPE.
Both raw TYPE views remain. Per-head byte identity is reported above.
No second manual TYPE read or whole-body manual read is claimed.
All approved helper names and four private markers are absent from PUBLIC TYPE.
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

Preservation covers 106098 files/modes and 3643 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, proofs, drafts,
counterexamples and optimized code remain. Extra H28 Haskell archives must match baseline bytes.
Nine document inverses preserve all old text.
The original Audit has 3133 lines and SHA 393f9390294b78b458a9d8529a1bf405836bbba6af1f0cec4b6f310a27feca8d.
Its sole edit is the new module import. FINDINGS retains the repair index FIRST.
PR #65 and PR #97 remain fixed. No Haskell repair or runtime change is added.

H27 was pushed and remote-verified at b796e8e660a73ac328d41cad53c61099ba79d93f.
The standing user authorization permits further pushes to formalize.
H28 seal and push are not claimed here.
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
note = ROOT / 'lean/notes-current-comparison-native-covered.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
