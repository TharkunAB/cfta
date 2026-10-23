exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
import sys
review = Path('/tmp/mcfta-cluster-admission-boundary-full-audit')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
name = 'SourceCurrentOriginalRowClusterAdmissionBoundary'
source = HERE / (name + '.lean')
selected = load(HERE / 'boundary-selected-source-gate.json')
assert sha(source) == selected['source_sha256'] == 'd610d762a429313d324e6184265d793312a2e8ac05d24c936dc350a4b5be8b93'
assert (HERE / 'boundary-strict3.log').read_bytes() == b''
receipt = load(HERE / 'boundary-FULL1.json')
assert receipt['exit_code'] == 0
assert sha(HERE / receipt['source']) == receipt['sha256']
assert load(HERE / 'boundary-FULL1.limits.json') == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
readback_path = HERE / 'public-readback/cluster-admission-boundary-full-readback.json'
readback = load(readback_path)
assert readback['source_sha256'] == sha(source) and readback['source_lines'] == 199
assert readback['log_sha256'] == sha(HERE / 'boundary-FULL1.log')
assert readback['printer_sha256'] == receipt['sha256']
assert len(readback['heads']) == 1
head = readback['heads'][0]
assert head['head'] == 'MicroCFTA.' + name + '.boundary_complete'
assert head['check_print_type_byte_identity'] is True and head['check_print_type_lexical_identity'] is True
assert head['actual_axioms_within_standard_allowed'] and head['private_public_type_names'] is False
type_path = HERE / 'public-readback/cluster-admission-boundary-boundary_complete-public-type.txt'
assert sha(type_path) == head['checked_type_sha256'] == 'f1870d184403bb847a1cf67ddbddcb021dd923a6092e5ebf2feb5b23e9225f44'
assert len(type_path.read_bytes()) == 98638 and len(type_path.read_bytes().splitlines()) == 1056
archive(review, 'boundary-full-audit')
target = ROOT / 'lean/MicroCFTA' / (name + '.lean')
assert not target.exists()
shutil.copy2(source, target)
assert sha(target) == sha(source)
save('root-boundary-full-review.json', {
    'status': 'ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED',
    'source_sha256': sha(source), 'source_lines': 199,
    'root_manual_complete_TYPEs': True,
    'root_type_read_ranges': [[1, 180], [181, 360], [361, 540], [541, 720], [721, 900], [901, 1056]],
    'independent_complete_TYPE_review_sha256': sha(review / 'review.json'),
    'TYPEs': {'boundary_complete': {'sha256': sha(type_path), 'bytes': 98638, 'logical_lines': 1056, 'actual_axioms': head['actual_axioms']}},
    'readback_sha256': sha(readback_path),
    'same_fixed_inventory_initial_domains_width_and_before_after_packet': True,
    'boundary_run_and_positive_prefix_and_strictly_smaller_next_are_outputs': True,
    'no_future_Room_or_result_oracle': True,
    'BODY_review': 'Original BODY bytes retained and programmatically checked. No manual whole BODY review is claimed.',
    'next_job': 'Focused build must produce the importable boundary artifact before outer strict compilation.',
    'aggregate_Audit': 'Deferred until the complete selected admission cohort.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: complete actual boundary TYPE accepted and source installed')
