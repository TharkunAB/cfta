exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-group-admission-declaration-plan')
checked_package(owner, 'd13ed06d393b4c6f1d95dd391e2890b3c723cfcffe4f2397ecc21374baa93dd5', 'e525c308510452610ecd0778a2f956f045e35aeb00a3bb7b66cbd85c4a0c315a')
audit = Path('/tmp/mcfta-group-admission-declaration-audit')
checked_package(audit, 'da7edfc54bb700d40dafdd8f7a9adc456aa9badbacc3860c36ebfdcb3edf6910', '622b1e585ff2079085da06195567681e630cf56ad4896e9bf67fd6b1e6989e9b')
assert load(audit / 'review.json')['status'] == 'CLEAR'
schema = load(owner / 'declaration-schema.json')
assert schema['public_heads'] == ['groups_admitted'] and schema['whole_source_hard_stop'] == 180
assert schema['private_helpers'] == schema['global_definitions'] == schema['typed_show_fragments'] == []
assert schema['local_have_names'] == ['reversed', 'included', 'found', 'contents']
manifest = load(owner / 'contracts.json')
assert len(manifest) == 10 and all(isinstance(value, str) for value in manifest.values())
layout = load(owner / 'insertion-map.json')['compiled_fragments']
assert list(manifest) == [item['file'] for item in layout]
for item in layout:
    assert sha(owner / item['file']) == item['sha256'] == manifest[item['file']]
    assert len((owner / item['file']).read_bytes().splitlines()) == item['lines']
target = Path('/tmp/mcfta-group-admission-root-declaration-gate.json')
assert not target.exists()
gate = dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    module='SourceCurrentOriginalRowGroupAdmission', public_heads=['groups_admitted'],
    contracts_sha256=sha(owner / 'contracts.json'), insertion_map_sha256=sha(owner / 'insertion-map.json'),
    independent_review_sha256=sha(audit / 'review.json'), root_whole_context_lines_read=28,
    root_whole_public_header_lines_read=38, root_all_local_contracts_and_generated_IH_read=True,
    source_target=[130,165], whole_source_hard_stop=180, default_declaration_limits=True,
    all_linters=True, same_supplied_chain=True, future_resource_or_result_oracle=False,
    selected_body_authoring_accepted=True, compiler_activation_authorized=False,
    observed_at=__import__('datetime').datetime.now().astimezone().isoformat())
target.write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps(gate))
