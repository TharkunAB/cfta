exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
import sys
review = Path('/tmp/mcfta-cluster-admission-outer-full-audit')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
name = 'SourceCurrentOriginalRowClusterAdmission'
source = HERE / (name + '.lean')
assert sha(source) == '13d2fc71f5cb29a0c836954a2bec01de7d3569eff0797a6bda2ad7ca00374bc1'
assert (HERE / 'outer-strict1.log').read_bytes() == b''
receipt = load(HERE / 'outer-FULL1.json')
assert receipt['exit_code'] == 0 and sha(HERE / receipt['source']) == receipt['sha256']
assert load(HERE / 'outer-FULL1.limits.json') == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
readback_path = HERE / 'public-readback/cluster-admission-outer-full-readback.json'
readback = load(readback_path)
assert readback['source_sha256'] == sha(source) and readback['source_lines'] == 136
assert readback['log_sha256'] == sha(HERE / 'outer-FULL1.log')
assert readback['printer_sha256'] == receipt['sha256']
expected = [
    ('cluster_complete', 730, 64333, '116f9953111a9a6eebbe14d5c70293f31a79aeaa1d00e77c83652d638f23dd19'),
    ('completed_admitted', 644, 56642, '898012158320fcdc42bb1a9999fb9dab6561a34e538ee1f09f88ab8c3a20b281'),
]
assert len(readback['heads']) == len(expected)
types = {}
for head, (short, lines, size, digest) in zip(readback['heads'], expected, strict=True):
    assert head['head'] == 'MicroCFTA.' + name + '.' + short
    assert head['check_print_type_byte_identity'] is True and head['check_print_type_lexical_identity'] is True
    assert head['actual_axioms_within_standard_allowed'] and head['private_public_type_names'] is False
    path = HERE / ('public-readback/cluster-admission-outer-' + short + '-public-type.txt')
    assert sha(path) == head['checked_type_sha256'] == digest
    assert len(path.read_bytes()) == size and len(path.read_bytes().splitlines()) == lines
    types[short] = dict(sha256=digest, bytes=size, logical_lines=lines, actual_axioms=head['actual_axioms'])
archive(review, 'outer-full-audit')
target = ROOT / 'lean/MicroCFTA' / (name + '.lean')
assert not target.exists()
shutil.copy2(source, target)
assert sha(target) == sha(source)
save('root-outer-full-review.json', {
    'status': 'ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED',
    'source_sha256': sha(source), 'source_lines': 136,
    'root_manual_complete_TYPEs': True,
    'root_type_read_ranges': {'cluster_complete': [[1, 200], [201, 400], [401, 600], [601, 730]], 'completed_admitted': [[1, 200], [201, 400], [401, 600], [601, 644]]},
    'TYPE_display': 'Leading ASCII spaces removed for display only. All lines and tokens retained; raw files unchanged.',
    'independent_complete_TYPE_review_sha256': sha(review / 'review.json'),
    'TYPEs': types, 'readback_sha256': sha(readback_path),
    'producer_derives_actual_completion': True,
    'adapter_retains_supplied_fuel_kept_and_full_after': True,
    'no_future_Room_or_result_oracle': True,
    'BODY_review': 'Original BODY bytes retained and programmatically checked. No manual whole BODY review is claimed.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
cohort = [
    ('SourceCurrentOriginalRowClusterExecution', 'execution-strict2', 'execution-FULL1'),
    ('SourceCurrentOriginalRowClusterAdmissionBoundary', 'boundary-strict3', 'boundary-FULL1'),
    (name, 'outer-strict1', 'outer-FULL1'),
]
selected = {}
for module, strict, full in cohort:
    installed = ROOT / 'lean/MicroCFTA' / (module + '.lean')
    assert installed.read_bytes() == (HERE / (module + '.lean')).read_bytes()
    selected['lean/MicroCFTA/' + module + '.lean'] = dict(sha256=sha(installed), lines=len(installed.read_bytes().splitlines()), strict=strict, full=full)
save('selected-sources.json', selected)
save('frozen-modules.json', {Path(path).stem: record['sha256'] for path, record in selected.items()})
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
original = HERE / 'original-sources/Audit.original.lean.txt'
assert audit.read_bytes() == original.read_bytes()
assert sha(original) == '853386f7c9677a9f4d93520b2a2f77fe6ffc42553726c79243aba3d7e55782e2'
addition = b''.join(('import MicroCFTA.' + module + '\n').encode() for module, _strict, _full in cohort)
audit.write_bytes(addition + original.read_bytes())
assert audit.read_bytes().removeprefix(addition) == original.read_bytes()
save('root-cohort-audit-gate.json', {
    'status': 'ACCEPTED_ALL_SIX_PUBLIC_TYPES_FOR_SOLE_AGGREGATE_AUDIT',
    'selected_modules': 3, 'public_theorems': 6,
    'selected_sources_sha256': sha(HERE / 'selected-sources.json'),
    'audit_original_sha256': sha(original), 'audit_installed_sha256': sha(audit),
    'audit_addition_utf8': addition.decode(),
    'authorized_next_job': 'cluster-admission-audit1',
    'proof_commit_expected_paths': list(selected) + ['lean/MicroCFTA/Audit.lean'],
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: both outer TYPEs accepted; three-source cohort installed and sole aggregate Audit authorized')
