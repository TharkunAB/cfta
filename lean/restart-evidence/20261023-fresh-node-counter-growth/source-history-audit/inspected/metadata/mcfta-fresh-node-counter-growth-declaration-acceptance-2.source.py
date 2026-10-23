exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import sys
review_path, expected_pins, expected_freeze, expected_review = sys.argv[1:]
owner = Path('/tmp/mcfta-fresh-node-counter-growth-declaration-plan-v2')
review = Path(review_path)
checked_package(owner, '4f63db5b7fe40b44c9964ce612c23367274d1e06c6ec7f04a4f916fc829347c4', '2776b9d34a2d7337774fedec79364ef4be39e765a87f3f54110634db2f5e79b5')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review and load(review / 'review.json')['status'] == 'CLEAR'
contracts = load(owner / 'contracts.json')
old = HERE / 'declaration-plan'
assert len(contracts) == 10 and sum(len((owner / file).read_bytes().splitlines()) for file in contracts) == 47
for file in contracts:
    expected = (old / file).read_bytes()
    if file == 'private-bind.lean.txt':
        expected = b'omit [DecidableEq (EdgeKey Symbol Guard)] in\n' + expected
    assert (owner / file).read_bytes() == expected, file
for file in ['introduced-types.json','recursive-call-contracts.json','mutual-induction.json']:
    assert (owner / file).read_bytes() == (old / file).read_bytes()
assert load(HERE / 'strict1.json')['exit_code'] == 1
archive(owner, 'declaration-plan-v2')
archive(review, 'declaration-v2-audit')
gate = load(HERE / 'root-declaration-gate.json')
gate.update(contracts_sha256=sha(owner / 'contracts.json'), insertion_map_sha256=sha(owner / 'insertion-map.json'),
    independent_review_sha256=expected_review, compiled_fragment_lines=47, root_whole_private_header_lines_read=19,
    contract_root='declaration-plan-v2', previous_gate='root-declaration-gate.json',
    private_bind_omit_prefix_complete_read=True, unused_private_instance_removed=True,
    all_public_and_local_and_recursive_types_unchanged=True, strict1_retained=True,
    compiler_activation_authorized=False)
save('root-declaration-gate-v2.json',gate)
for old_name,new_name in [('root-full-tool-scope-gate.json','root-full-tool-scope-gate-v2.json'),
                          ('root-proof-verifier-scope-gate.json','root-proof-verifier-scope-gate-v2.json')]:
    scoped = load(HERE / old_name)
    scoped.update(previous_scope_gate=old_name, declaration_gate='root-declaration-gate-v2.json',
        declaration_gate_sha256=sha(HERE/'root-declaration-gate-v2.json'),contract_root='declaration-plan-v2',
        compiled_fragment_lines=47,private_header_lines=19,
        sole_declaration_delta='Omit the unused private bind instance.',generic_guards_preserved=True)
    save(new_name,scoped)
print('ACCEPTED exact omit-prefix declaration revision before new body; original gates and strict1 retained.')
