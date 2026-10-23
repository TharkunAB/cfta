exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
import sys
review = Path('/tmp/mcfta-cluster-admission-execution-full-audit')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
readback_path = HERE / 'public-readback/cluster-admission-execution-full-readback.json'
report = load(readback_path)
assert report['source_sha256'] == 'ee67ecabee46dd20e570eba723a816849c6d28f31a9e14d794eb4026a56092bb'
assert report['log_sha256'] == sha(HERE / 'execution-FULL1.log') == '5f8d71ad01d759a2642984cfb2cb9faf51967efe591729fc4627a3e4fc96b064'
assert report['log_bytes'] == 238840
assert len(report['retained_slices']) == 12
for relative, pin in report['retained_slices'].items():
    path = HERE / 'public-readback' / relative
    assert sha(path) == pin['sha256'] and path.stat().st_size == pin['bytes']
assert [h['head'].rsplit('.', 1)[1] for h in report['heads']] == ['yielded_add', 'done_stable', 'completed_unique']
types = {}
for head in report['heads']:
    assert head['check_print_type_identity'] and head['check_print_type_byte_identity']
    assert head['actual_axioms_within_standard_allowed']
    assert not head['private_public_type_names'] and head['private_namespace_helpers_checked'] == []
    short = head['head'].rsplit('.', 1)[1]
    path = HERE / 'public-readback' / ('cluster-admission-execution-' + short + '-public-type.txt')
    types[short] = {'sha256': sha(path), 'bytes': path.stat().st_size, 'logical_lines': len(path.read_text().splitlines()), 'actual_axioms': head['actual_axioms']}
archive(review, 'execution-full-audit')
source = HERE / (NAME + '.lean')
target = ROOT / 'lean/MicroCFTA' / (NAME + '.lean')
assert not target.exists() and sha(source) == report['source_sha256']
shutil.copy2(source, target)
assert sha(target) == report['source_sha256']
save('root-execution-full-review.json', {
    'status': 'ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED',
    'source_sha256': sha(source), 'source_lines': 64,
    'root_manual_complete_TYPEs': True, 'independent_complete_TYPE_review_sha256': sha(review / 'review.json'),
    'TYPEs': types, 'readback_sha256': sha(readback_path),
    'BODY_review': 'All original BODY bytes retained and programmatically checked. No manual whole BODY review is claimed.',
    'whole_root_owned_Lean_history_so_far': ['execution-strict1 failed on v1', 'execution-strict2 passed on v2', 'execution-FULL1 passed on v2'],
    'next_job': 'Focused lake build of this installed module is required to produce its importable artifact.',
    'aggregate_Audit': 'Deferred until the complete selected admission cohort.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: complete public types accepted; exact64-line module installed; focused import artifact build authorized')
