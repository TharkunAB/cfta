exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-cluster-admission-boundary-declaration-v2')
review = Path('/tmp/mcfta-cluster-admission-boundary-declaration-v2-audit')
checked_package(owner, '22ef52c79a111ec4d07f00dc901e8d7b0a99a99d643b4bf8a0448a4e4222a521', 'd9e983a00e93323472b839f68a3b736ee1c0a806312df11e3643252eac89daad')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
for name, digest in load(owner / 'contracts.json').items():
    assert sha(owner / name) == digest
old = HERE / 'boundary-declaration-plan'
changed = [name for name in load(owner / 'contracts.json') if (owner / name).read_bytes() != (old / name).read_bytes()]
assert changed == ['context.lean.txt', 'local-parentAdmitted.lean.txt']
assert (owner / 'ih-schema.lean.txt').read_bytes() == (old / 'ih-schema.lean.txt').read_bytes()
assert load(HERE / 'boundary-strict1.json')['exit_code'] == 1
archive(owner, 'boundary-declaration-v2')
archive(review, 'boundary-declaration-v2-audit')
gate = load(HERE / 'root-boundary-declaration-gate.json')
gate.update({
    'contracts_sha256': sha(owner / 'contracts.json'),
    'independent_review_sha256': sha(review / 'review.json'),
    'previous_root_gate_sha256': sha(HERE / 'root-boundary-declaration-gate.json'),
    'root_complete_two_fragment_repair_and_exact_inverse_read': True,
    'declaration_repair': 'Public explicit EdgeRequest.mk in notation; parenthesized inputs before .valid. Public proposition and IH are unchanged.',
    'body_authoring_authorized': True, 'compiler_activation_authorized': False,
    'default_declaration_limits': True, 'all_linters': True,
})
save('root-boundary-declaration-v2-gate.json', gate)
print('PASS: exact two-fragment declaration repair accepted before mathematical source rewrite')
