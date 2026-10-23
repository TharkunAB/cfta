exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
import sys
plan = Path('/tmp/mcfta-cluster-admission-execution-full-tool-plan')
owner = Path('/tmp/mcfta-cluster-admission-execution-full-preparation')
review = Path('/tmp/mcfta-cluster-admission-execution-full-tools-audit')
checked_package(plan, 'e0efaab20496cffbe7aee1fb8bb7073a32edc45913d66271900c798f554e1d9b', '3ebf72e5fe4d03aa48195c00e8c8894036dab4a5d5e0c5f55b3d867175ff8a66')
checked_package(owner, '70974c614be883dc03f44df99534165a316f783c7390e88bd672ba74025bde0c', '687d1a6183441c4f55d798e65fec6223c1900fed42d8bb90b9567fd164ef1788')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
selected = load(HERE / 'execution-selected-source-gate.json')
assert selected['status'] == 'ACCEPTED_STRICT_SOURCE'
bindings = load(owner / 'binding-map.json')
for key in ['contract_manifest', 'root_declaration_gate', 'strict_receipt', 'strict_log', 'strict_source']:
    record = bindings[key]
    assert sha(Path(record['path'])) == record['sha256']
    assert Path(record['path']).stat().st_size == record['bytes']
archive(plan, 'execution-full-tool-plan')
archive(owner, 'execution-full-preparation')
archive(review, 'execution-full-tools-audit')
installed = {}
for source_name, target_name, digest in [
    ('prepare-selected-full.py', 'prepare-execution-full.py', '02325e00fbe4c8120c8c839fd31ced0d1c533a55cb61a3e2c3c379f30b08054c'),
    ('check-full-public.py', 'check-execution-full-public.py', '2cf37155737cd5ea1149439e837ee828d8948c923b26201d4797579ca09717fe'),
]:
    source = owner / 'selected' / source_name
    target = HERE / target_name
    assert not target.exists() and sha(source) == digest
    shutil.copy2(source, target)
    assert sha(target) == digest
    installed[target_name] = digest
save('root-execution-full-tools-gate.json', {
    'status': 'ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',
    'root_whole_selected_lines_read': 198, 'diagnostic_tail_lines': 20,
    'independent_review_sha256': sha(review / 'review.json'), 'installed_tools': installed,
    'source_sha256': selected['source_sha256'], 'public_heads': selected['public_heads'],
    'materializer_activation': True, 'sole_FULL_activation': True,
    'reader_activation_after_actual_FULL': True,
    'closing_scope_correction': 'This gate concerns the operational prerequisite only. The final cohort and proof commit file count remain undecided.',
    'new_proof_result_claimed': False,
})
print('PASS: exact reviewed FULL preparation/reader installed for actual clean strict2')
