import runpy
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

package = Path('/tmp/mcfta-comparison-native-covered-pending-tools')
checked_package(package,
    'f34bb27fd9d20f871f177798b716f06754d219fbac490673200c205d4b16cab4',
    '7d1fecc8b1bbba4ba0352dcd712331326c63305251afcc1a641c27a29d64cf29')
audit = Path('/tmp/mcfta-comparison-native-covered-pending-tools-audit')
checked_package(audit,
    '768598562062c18604b632fb5de38d62518d3c54a2f927b3130f30498fb6fa0e',
    '3c6d3d3c48f1a45a3e1c219c5801bdd65e76331b8f82149963353380237d8f55')
assert sha(audit / 'review.json') == '8621eea6238fe1353c008cc7e6c135d1961cf29e15d6fab573d75657e93c24fb'
assert load(audit / 'review.json')['status'] == 'SOURCE_ONLY_PENDING_TEMPLATES_CLEAR'
assert sha(package / 'selected-scripts.json') == '11a53e366c7f317aa0b56f7b5f79fdc702ad8745c5e4447aa7ca72233e611149'
metrics = load(package / 'selected-scripts.json')
assert metrics['total_lines'] == 507 and metrics['AST_assertions'] == 143
assert len(metrics['scripts']) == 8 and metrics['proof_specific_verify_proofs_excluded']
assert load(package / 'pending-data-slots.json')['slot_count'] == 23
archive(package, 'pending-tools')
archive(audit, 'pending-tools-audit')
save('root-pending-tools-review.json', dict(status='ROOT_SOURCE_ONLY_PENDING_TEMPLATES_ACCEPTED',
    whole_selected_sources_read=8, lines=507, retained_assertions=143, all_eight_deltas_read=True,
    pending_slots=23, independent_review_sha256=sha(audit / 'review.json'),
    proof_verifier_excluded=True, execution_authorized=False,
    actual_binding_and_proof_verifier_gate_required=True, whole_goal_complete=False))
print(json.dumps(dict(status='PASS', pending_tools=8, lines=507, pending_slots=23, execution_authorized=False)))
