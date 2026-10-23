exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import re
owner = Path('/tmp/mcfta-cluster-admission-outer-source-v1')
review = Path('/tmp/mcfta-cluster-admission-outer-body-audit')
checked_package(owner, '0e78da6b5819655ef3cddb7190f56487f424802b3e5b74d76f2b5fa643ff7e2c', '55967e52b1184ac91956b6944b0af3219a33922eac4ab7950c0cd862cd101eaf')
checked_package(review, 'ed34493095e49f57890172765fbba6f77e382e50419f517ecb0a97d8c607c574', '098ede2292246f54857bf3f551647118a36d86cd15c5c226bc5f3bc61b75a8b4')
name = 'SourceCurrentOriginalRowClusterAdmission'
source = owner / (name + '.lean')
raw = source.read_bytes()
assert sha(source) == '13d2fc71f5cb29a0c836954a2bec01de7d3569eff0797a6bda2ad7ca00374bc1'
assert len(raw.splitlines()) == 136 <= 230
gate = load(HERE / 'root-outer-declaration-gate.json')
assert gate['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
contracts = HERE / 'outer-declaration-plan-v3'
assert sha(contracts / 'contracts.json') == gate['contracts_sha256']
positions = []
for filename, digest in load(contracts / 'contracts.json').items():
    fragment = (contracts / filename).read_bytes().rstrip(b'\n')
    assert sha(contracts / filename) == digest
    assert raw.count(fragment) == 1, filename
    positions.append(raw.index(fragment))
assert len(positions) == 11 and positions == sorted(positions)
assert re.findall(r'(?m)^theorem (\w+)', raw.decode()) == ['cluster_complete', 'completed_admitted']
assert re.findall(r'(?m)^\s+have (\w+)\s*:', raw.decode()) == ['pivotMember', 'tailMembers', 'smaller', 'prefixRun']
assert not re.search(r'(?m)^\s*(?:private|def|lemma|let|set_option)\b', raw.decode())
audit = load(review / 'review.json')
assert audit['status'] == 'CLEAR' and audit['source_sha256'] == sha(source)
archive(owner, 'outer-source-v1')
archive(review, 'outer-body-audit')
save('root-outer-body-gate.json', {
    'status': 'ACCEPTED_EXACT_BODY_PENDING_BOUNDARY_DEPENDENCY_READINESS',
    'module': name, 'source_sha256': sha(source), 'source_lines': 136,
    'root_whole_source_lines_read': 136, 'exact_ordered_contracts': 11,
    'root_complete_generated_IH_schema_read': True,
    'independent_review_sha256': sha(review / 'review.json'),
    'public_heads': gate['public_heads'],
    'no_extra_helpers_or_local_types': True,
    'default_declaration_limits': True, 'all_linters': True,
    'compiler_activation_authorized': False,
    'dependency': 'Boundary FULL TYPE acceptance, installation and focused build remain required.',
})
print('PASS: exact independently reviewed outer body accepted; compiler remains gated')
