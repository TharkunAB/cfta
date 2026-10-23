exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
import sys
plan = Path('/tmp/mcfta-cluster-admission-outer-full-tool-plan')
owner = Path('/tmp/mcfta-cluster-admission-outer-full-preparation')
review = Path('/tmp/mcfta-cluster-admission-outer-full-tools-audit')
checked_package(plan, '38b9a2b5707207ea51669e7b29b77a30ad53f57a1dba08e60e3ebc93713aa75b', '992e869c0661fab422e34f462a8a2c704880217fe3513cba276bb722f26b13ab')
checked_package(owner, '6c060d75a87195aa8feab6b6fd51c49c28ef7ffa92a4d76f6d23c45478233dca', '42d0ee41938a706168fb3ed5206cd0b716aa7eaac503e8237925edee7ee2eaed')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
selected = load(HERE / 'outer-selected-source-gate.json')
assert selected['status'] == 'ACCEPTED_STRICT_SOURCE'
assert selected['source_sha256'] == '13d2fc71f5cb29a0c836954a2bec01de7d3569eff0797a6bda2ad7ca00374bc1'
args = load(owner / 'materializer-arguments.json')
assert args['arguments'][0] == selected['selected_strict'] == 'outer-strict1'
assert args['source_sha256'] == selected['source_sha256']
assert sha(HERE / 'outer-strict1.json') == args['receipt_sha256'] == selected['receipt_sha256']
assert (HERE / 'outer-strict1.log').read_bytes() == b''
archive(plan, 'outer-full-tool-plan')
archive(owner, 'outer-full-preparation')
archive(review, 'outer-full-tools-audit')
assessment = Path('/tmp/mcfta-cluster-admission-next-lift-assessment')
checked_package(assessment, 'd2247a12fd70165caac3b66bdcca27f411e0c7efc0577389a96203805a2060aa', 'a94c752b86af9e091fdf43164df41d91a56056bd19af0fa9caa66712bd8c5b77')
archive(assessment, 'next-lift-assessment')
installed = {}
for source_name, target_name, digest in [
    ('prepare-selected-full.py', 'prepare-outer-full.py', '43a3e6e1a98a7351c70b22492a1e6b4a0c32dcc0ed9adf16ab403606d13aa4bd'),
    ('check-full-public.py', 'check-outer-full-public.py', '1a59f0fabc869b99ff8dc498d878d464937b6d12b21f855d197b35a29f05fbe8'),
]:
    source = owner / 'selected' / source_name
    target = HERE / target_name
    assert not target.exists() and sha(source) == digest
    shutil.copy2(source, target)
    assert sha(target) == digest
    installed[target_name] = digest
save('root-outer-full-tools-gate.json', {
    'status': 'ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',
    'root_whole_selected_lines_read': 201,
    'root_complete_forward_inverse_diff_read': True,
    'diagnostic_tail_lines': 17,
    'independent_review_sha256': sha(review / 'review.json'),
    'installed_tools': installed,
    'source_sha256': selected['source_sha256'],
    'public_heads': selected['public_heads'],
    'materializer_activation': True, 'sole_FULL_activation': True,
    'reader_activation_after_actual_FULL': True,
    'source_only_next_lift_assessment_retained': True,
    'new_proof_result_claimed': False,
})
print('PASS: exact reviewed outer FULL preparation and reader installed')
