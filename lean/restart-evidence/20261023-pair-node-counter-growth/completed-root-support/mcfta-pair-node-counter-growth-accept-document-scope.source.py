exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-pair-node-counter-growth-document-scope-plan')
peer = Path('/tmp/mcfta-pair-node-counter-growth-document-scope-review')
checked_package(owner,'4363a238472f55cc5e1c88ec93e8d70c6b81e1bfe8f7183d4e2749ead81371a9','a9fc9ffab6da9243c8ac8b5fced6d11280449ff4a91e5e75ce1a4d5a11dee7ca')
checked_package(peer,'c8cb34f039a80c14b79bb87f6d16b799d9046a1d8e2403c0ca535bf8a1fc3645','5c21089882a5824c9a433d3e57b9704652f90f0ee4473afbb913b77be0dfae60')
assert sha(peer / 'review.json') == '000fed85c33022b32ae479bc2be236f31dea0a1b4b686d9fb225d5010826edea'
assert load(peer / 'review.json')['status'] == 'CLEAR'
archive(owner,'document-scope-plan')
archive(peer,'document-scope-audit')
save('root-document-scope-gate.json',dict(status='ACCEPTED_SOURCE_ONLY_DOCUMENT_WRITER_AND_PAYLOAD_SCOPE',
    module=NAME,root_complete_88_line_basis_and_29_line_plan_and_25_guards_read=True,
    selected_target=88,selected_hard_stop=100,all_generic_guards_retained=True,
    nine_exact_LF_prefix_inverses=True,FINDINGS_repair_index_first=True,
    actual_both_saved_modes_and_exact_proof_commit_before_execution=True,
    open_work_qualifies_new_counter_bound_composition_and_preserves_older_H23_results=True,
    independent_review_sha256=sha(peer / 'review.json'),selected_authoring_authorized=True,
    selected_activation_authorized=False,whole_writer_and_payload_peer_review_required=True))
print('Accepted document source and payload authoring scope with precise H23 composition wording.')
