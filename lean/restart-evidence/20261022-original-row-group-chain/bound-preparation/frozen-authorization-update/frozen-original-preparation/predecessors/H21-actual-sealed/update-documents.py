import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE_SHA = '3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba'
SOURCE_LINES = int('89')
assert 0 < SOURCE_LINES <= 240
strict, full, audit_stem = 'prepend-grouping-strict-3', 'prepend-grouping-public-1', 'prepend-grouping-audit-1'
metrics = {
    'actual_jobs': int('5'),
    'source_jobs': int('4'),
    'audit_jobs': int('1'),
    'failed_jobs': int('2'),
    'warned_source_exit_zero_jobs': int('0'),
    'rejected_public_type_jobs': int('0'),
    'audit_build_jobs': int('3638'),
    'audit_dependencies': int('75494'),
}
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == 'd0cf685f461430a7c608ceb3b76da0fe568e4d84'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == proof
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'formalize'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
gate = json.loads((HERE / 'selected-source-gate.json').read_text())
source_path = 'lean/MicroCFTA/SourceCurrentPrependGrouping.lean'
assert gate['status'] == 'ROOT_ACCEPTED' and gate['path'] == source_path
source = (ROOT / source_path).read_bytes()
assert hashlib.sha256(source).hexdigest() == gate['sha256'] == SOURCE_SHA
assert source == (HERE / gate['snapshot']).read_bytes() and len(source.splitlines()) == gate['lines'] == SOURCE_LINES
assert source == (HERE / (strict + '.source.lean')).read_bytes() and (HERE / (strict + '.log')).read_bytes() == b''
assert json.loads((HERE / (strict + '.json')).read_text())['exit_code'] == 0
raw = (HERE / (full + '.log')).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '215b81824a227e47375a236476dd83092a5bf1c21a421a85e835bdd3e75e61a8'
assert json.loads((HERE / (full + '.json')).read_text())['exit_code'] == 0
readback = json.loads((HERE / 'public-readback/prepend-grouping-full-readback.json').read_text())
assert readback['source_sha256'] == SOURCE_SHA and readback['source_lines'] == SOURCE_LINES
assert readback['log_sha256'] == hashlib.sha256(raw).hexdigest() and readback['log_bytes'] == len(raw)
head_specs = json.loads('[["insertWith", "48d0904f048cbeafc8e95f8b22efc2393f403c1732296c487e69c9bde0e1c2be", "48d0904f048cbeafc8e95f8b22efc2393f403c1732296c487e69c9bde0e1c2be", "2070c90b3a20e08bc6ee18540c8a6c382e22c8cac3dc784571aea6339a6e2029", true, "public-readback/prepend-grouping-insertWith-public-type.txt", "public-readback/prepend-grouping-insertWith-printed-public-type.txt", "[]"], ["fromRows", "094eb0b94d3ffba52ac789f9f51dcbfa5a44f017b4b33e5cf5ac8e165512ae28", "094eb0b94d3ffba52ac789f9f51dcbfa5a44f017b4b33e5cf5ac8e165512ae28", "2de1facfaf02162c1673ff85572a91a23c07ff45ee0bd2e852e5bb9749e0df0b", true, "public-readback/prepend-grouping-fromRows-public-type.txt", "public-readback/prepend-grouping-fromRows-printed-public-type.txt", "[]"], ["reverseTable", "1c8a53b41b8713b00c11021bc6eceb70ac44f344491d7d669fc0f57c9c914528", "1c8a53b41b8713b00c11021bc6eceb70ac44f344491d7d669fc0f57c9c914528", "3ca033ceb30ce55d6e40174e64c6cfa2b7a678145592b624c9a49b75b53b551a", true, "public-readback/prepend-grouping-reverseTable-public-type.txt", "public-readback/prepend-grouping-reverseTable-printed-public-type.txt", "[]"], ["pair_fold", "9dc4d1e79df4da3e0ead7a744b916ab00c8352344aa090cbfe469a9a4988d800", "80591714a25308241133eda0250a552e996f6531f7cbfa031bdf5338640d1061", "c94234bcbd7ae0ee1d53048469a3f8ef616122f57b5cb21f7b80fb97698fe824", false, "public-readback/prepend-grouping-pair_fold-public-type.txt", "public-readback/prepend-grouping-pair_fold-printed-public-type.txt", "[\\"propext\\"]"], ["reverse_insert_singleton", "fd13a4e124d61c37b4c120aab3211187fbe18ab2f5c8a3a355340969daf69f05", "2647b3b5bfd2290c719ba98df5e8537b7afeaf8756b68064ddd23336c092b2bb", "a88381f5ad81acb49e545d34b770ee94b75b4433699d1511a87978265a58eff1", false, "public-readback/prepend-grouping-reverse_insert_singleton-public-type.txt", "public-readback/prepend-grouping-reverse_insert_singleton-printed-public-type.txt", "[\\"Quot.sound\\", \\"propext\\"]"], ["reverse_fold", "e7abc72eb5ae11313b0f756be9443ce3b225a81bf3eedd247face7aaa24db0d3", "e7abc72eb5ae11313b0f756be9443ce3b225a81bf3eedd247face7aaa24db0d3", "4026de9a15f3bdd86402abe720a0d58f3368e46c4ff381243690d5c53426669a", true, "public-readback/prepend-grouping-reverse_fold-public-type.txt", "public-readback/prepend-grouping-reverse_fold-printed-public-type.txt", "[\\"Quot.sound\\", \\"propext\\"]"], ["reverse_fromRows", "3344b088d26e80b94b33956fa84b16cb6af5408602461acb91fda1a3d6b72a30", "3344b088d26e80b94b33956fa84b16cb6af5408602461acb91fda1a3d6b72a30", "de6c752d1da376b684d75a2c5ba95eee50523520c493617dcc1f678335980209", true, "public-readback/prepend-grouping-reverse_fromRows-public-type.txt", "public-readback/prepend-grouping-reverse_fromRows-printed-public-type.txt", "[\\"Quot.sound\\", \\"propext\\"]"], ["iteration_reverse", "15c4e831693315e33e19ee2140d5f757843e1d25833c40ca89f21a425e58a4b6", "15c4e831693315e33e19ee2140d5f757843e1d25833c40ca89f21a425e58a4b6", "094b6bee174403be3e74712d95b8a924924446b2e6241f5efc54f52a2800116c", true, "public-readback/prepend-grouping-iteration_reverse-public-type.txt", "public-readback/prepend-grouping-iteration_reverse-printed-public-type.txt", "[\\"Quot.sound\\", \\"propext\\"]"], ["iteration_permutation", "8c2e931f0f424be14138db69cb52d15859f0cb4928faa4ba90abae6bca0175a9", "8c2e931f0f424be14138db69cb52d15859f0cb4928faa4ba90abae6bca0175a9", "b6696c3f80179ca3c95ac10b10fdbdd6c2180d24b2f3cfdab4b99dde6bc7518b", true, "public-readback/prepend-grouping-iteration_permutation-public-type.txt", "public-readback/prepend-grouping-iteration_permutation-printed-public-type.txt", "[\\"Classical.choice\\", \\"Quot.sound\\", \\"propext\\"]"]]')
assert [spec[0] for spec in head_specs] == ['insertWith', 'fromRows', 'reverseTable', 'pair_fold', 'reverse_insert_singleton', 'reverse_fold', 'reverse_fromRows', 'iteration_reverse', 'iteration_permutation']
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
    assert head['head'] == 'MicroCFTA.SourceCurrentPrependGrouping.' + short
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
    assert proof_report['audit_log_sha256'] == 'ac7c811b03802079e982a193b2256289c418f7c5449cc52176ddaaa107580fff'
audit = (HERE / (audit_stem + '.log')).read_bytes()
assert hashlib.sha256(audit).hexdigest() == proof_report['audit_log_sha256'] == 'ac7c811b03802079e982a193b2256289c418f7c5449cc52176ddaaa107580fff'
assert json.loads((HERE / (audit_stem + '.json')).read_text())['exit_code'] == 0
assert f"Build completed successfully ({metrics['audit_build_jobs']} jobs).".encode() in audit
assert f"{metrics['audit_dependencies']} MicroCFTA theorems".encode() in audit

type_summary = '\n'.join(
    f"{short} TYPE: {len(data.splitlines())} logical lines, {data.count(bytes([10]))} LF, {len(data)} bytes, {len(data.decode())} characters.\n"
    f"{short} raw checked SHA `{heads[short]['checked_type_sha256']}`; printed {len(printed_types[short])} bytes, SHA `{heads[short]['printed_type_sha256']}`.\n"
    f"{short} raw byte identity: {heads[short]['check_print_type_byte_identity']}; lexical identity: {heads[short]['check_print_type_lexical_identity']}; canonical SHA `{heads[short]['canonical_type_sha256']}`.\n"
    f"{short} actual axioms: {', '.join(heads[short]['actual_axioms']) or 'none'}."
    for short, data in checked_types.items())
update = f'''## Ordered symbol buckets for later group traversal

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-prepend-grouping.md`.

The selected SourceCurrentPrependGrouping declarations establish the reviewed
pure singleton-prepend, final reversal and finite iterator bridge.
Keys use equality. Each normalized bucket keeps its full input order and
all repeated occurrences. The outer bucket order remains unspecified.
The proof retains absent versus stored optional buckets.
It reuses the existing generic ordered grouping and iterator contracts.
This is not a refinement of Haskell HashMap storage or lazy evaluation.
No actual all-symbol traversal or new state/resource producer is claimed.

H20 preserves physical union language for one original symbol group.
All-symbol traversal, reconstruction, generated parents, public Mu/full pass,
practical width, solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Preservation covers 93582 baseline files/modes, 298 baseline Haskell files
and 207 active package files. FINDINGS keeps its repair index FIRST.
The approved 12-commit payload was pushed and verified at 562120d456.
Eight newer local commits at the H21 start need fresh exact-payload approval.
This checkpoint stays LOCAL_ONLY and performs no network command.
'''
findings = update
focused = f'''# Singleton prepend, final reversal and finite iterator transport

Updated: {now}. Proof checkpoint: `{proof}`. Start: `{start}`.

The selected reviewed declarations in SourceCurrentPrependGrouping provide
pure bucket and iterator laws for a generic key and item type.
Singleton insertion prepends new rows to the old optional bucket.
Reversing every final bucket gives the existing ordered append-fold table.
None and Some remain distinct. Every matching input occurrence remains.
Finite iterator transport preserves exact lookup and unique emitted keys.
The result permits an arbitrary outer order with exact within-bucket order.
No HashMap implementation or Haskell state/evaluation refinement is claimed.
No native request, group execution, new Room, reset or wider caller is added.

H20's checked one-symbol-group completion and physical union iff remain unchanged.
A later actual all-symbol traversal must retain its evolving packet and global history.
That traversal is not proved here. Generated parents, public Mu/full pass,
practical width, solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined theorem. The whole goal is incomplete.

Selected source: {SOURCE_LINES} lines, SHA `{SOURCE_SHA}`.
Selected clean strict: `{strict}`. Selected FULL: `{full}`.
Strict has a literal-empty log. Default declaration limits and all linters remain.
The source has a hard240-line limit. Diagnostics follow the complete module.
FULL retains {len(raw)} raw bytes. Complete check/print TYPEs agree after ASCII whitespace normalization.
{type_summary}
Root and an independent reviewer read each complete checked public TYPE.
Both raw TYPE views remain. Per-head byte identity is reported above. No second manual TYPE read is claimed.
All four private markers and recorded helper names are absent from TYPE.
Whole bodies remain retained and checked programmatically, not wholly read by hand.

The actual ledger has {metrics['actual_jobs']} Lean/Lake commands:
{metrics['source_jobs']} source and {metrics['audit_jobs']} Audit commands,
{metrics['failed_jobs']} failures, {metrics['warned_source_exit_zero_jobs']}
warned source exit-zero commands and {metrics['rejected_public_type_jobs']}
rejected PUBLIC TYPE commands. All inputs, raw logs and repair history remain.
The first reader stopped on TYPE wrapping. Its failed metadata artifacts remain.
The revised reader retains both raw views. No second FULL is run.
Metadata work creates no proof command. Audit has {metrics['audit_build_jobs']}
jobs and {metrics['audit_dependencies']} theorem dependencies.
This writer claims no seal or local publication success.

Preservation covers 93582 files/modes and 3636 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, proofs, drafts,
counterexamples and optimized code remain. Extra H21 Haskell archives must
match baseline source bytes. Nine document inverses preserve all old text.
The original Audit has 3126 lines and SHA 69e0e42c6e36fbe4cf9868df0582642fe2bf2a6df7c1ad3af4fae169445f6dd3.
Its sole edit is the new module import. FINDINGS retains the repair index FIRST.
PR #65 and PR #97 remain fixed. No Haskell repair or runtime change is added.

The approved 12-commit payload was pushed and verified at 562120d456.
Eight newer local commits at this start are outside that approval.
A future exact payload needs fresh approval. Old pending-12 notes are historical.
The checkpoint stays LOCAL_ONLY/PENDING_USER_APPROVAL.
The local publisher retains seal, scoped staging and filesystem/index/HEAD checks.
It performs no network command.
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
note = ROOT / 'lean/notes-current-prepend-grouping.md'
assert not note.exists()
note.write_text(focused)
print('Updated nine documents and focused note. All prior text remains.')
