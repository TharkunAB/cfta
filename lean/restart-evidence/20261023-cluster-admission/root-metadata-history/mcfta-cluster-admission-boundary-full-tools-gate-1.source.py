exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
packages = [
    ('/tmp/mcfta-cluster-admission-boundary-full-tool-plan', '8a60ad95027f994e9cea19619282b5f438160c923d4c9820606cbf0d8b4148f1', '04286860cbd03d16b8cd4891d0066c4495cce7782a3f8f5e48f0bf2749ba8fa9', 'boundary-full-tool-plan'),
    ('/tmp/mcfta-cluster-admission-boundary-full-preparation', 'eee08f604726cc842d0e10f14f196b80059dade105867c7c98c1b56319770256', 'f8c571303d2649178db41db52d144093f6723d237f440a1e9c3b3cc14200e08e', 'boundary-full-preparation-v2-historical'),
    ('/tmp/mcfta-cluster-admission-boundary-full-preparation-v3', '571100587f2bc9cdc41453c1bf4158e1368b802fe34c81dbb229f90fc708b8de', '4f68a84c78b175eca08206f2ee3d0174e2754864e5d3158df461e4bc18697c22', 'boundary-full-preparation-v3'),
    ('/tmp/mcfta-cluster-admission-boundary-full-v3-audit', '129f392a2732db3b81bad84a2aa527c0c95c5f0dfb065f23dc74180bcc33bcf2', '1f2231dd367b26b7d3970d8b8fbc551ad9ca0bafe2b32e70112471e378d5e2a4', 'boundary-full-tools-v3-audit'),
]
for path, pins, frozen, _archive in packages:
    checked_package(Path(path), pins, frozen)
owner = Path(packages[2][0])
review = Path(packages[3][0])
assert load(review / 'review.json')['status'] == 'CLEAR'
selected = load(HERE / 'boundary-selected-source-gate.json')
assert selected['status'] == 'ACCEPTED_STRICT_SOURCE'
assert selected['source_sha256'] == 'd610d762a429313d324e6184265d793312a2e8ac05d24c936dc350a4b5be8b93'
assert selected['selected_strict'] == 'boundary-strict3'
args = load(owner / 'materializer-arguments.json')
assert args['source_sha256'] == selected['source_sha256']
assert sha(Path(args['receipt'])) == args['receipt_sha256'] == selected['receipt_sha256']
assert sha(Path(args['source'])) == args['source_sha256']
assert (HERE / 'boundary-strict3.log').read_bytes() == b''
for path, _pins, _frozen, archive_name in packages:
    archive(Path(path), archive_name)
installed = {}
for source_name, target_name, digest in [
    ('prepare-selected-full.py', 'prepare-boundary-full.py', '02daac93bf288fadb98ea414e5c00814e17d6a04e1c67861f4958f7e9409105c'),
    ('check-full-public.py', 'check-boundary-full-public.py', '82eeccde421f570e7b83f8c4781b397dd2b69467b40b7ab03fa187dbf692f5d0'),
]:
    source = owner / 'selected' / source_name
    target = HERE / target_name
    assert not target.exists() and sha(source) == digest
    shutil.copy2(source, target)
    assert sha(target) == digest
    installed[target_name] = digest
save('root-boundary-full-tools-gate.json', {
    'status': 'ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',
    'root_whole_selected_lines_read': 201,
    'root_complete_forward_inverse_diff_read': True,
    'diagnostic_tail_lines': 14,
    'independent_review_sha256': sha(review / 'review.json'),
    'installed_tools': installed,
    'source_sha256': selected['source_sha256'],
    'public_heads': selected['public_heads'],
    'materializer_activation': True,
    'sole_FULL_activation': True,
    'reader_activation_after_actual_FULL': True,
    'historical_v2_preparation_never_activated': True,
    'new_proof_result_claimed': False,
})
print('PASS: reviewed V3 boundary FULL preparation and reader installed')
