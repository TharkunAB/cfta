exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-cluster-admission-proof-verifier-preparation-v2')
checked_package(owner, '98b78536a47e0d320a4ae191c7cddac07b313f2b5640355973546b7dd2393965', '5884d9ca28274053d98754ca94206c4c7948bd77a17e308bfaeed9f1f1af68f8')
audit = Path('/tmp/mcfta-cluster-admission-proof-verifier-v2-audit')
expected_pins, expected_frozen, expected_review = sys.argv[1:]
assert all(len(value) == 64 and set(value) <= set('0123456789abcdef') for value in sys.argv[1:])
checked_package(audit, expected_pins, expected_frozen)
assert sha(audit / 'review.json') == expected_review
review = load(audit / 'review.json')
assert review['status'] == 'CLEAR'
assert sha(owner / 'verify-proofs.py') == 'cdf6c6b0d27daba77349d16c9b84f3548659bdbf89e013781f140c1f1b283bce'
assert sha(owner / 'bound-data.json') == 'a459946233210efb26d9366b60acdde473686e171d4d209b793985eb455efbc9'
assert len((owner / 'verify-proofs.py').read_bytes().splitlines()) == 387
assert load(HERE / 'root-proof-verifier-v2-repair-scope-gate.json')['selected_v2_authoring_accepted']
assert load(HERE / 'root-source-history-revision-review.json')['mathematical_sources_unchanged']
old = load(owner / 'frozen-v1/bound-data.json')
new = load(owner / 'bound-data.json')
assert {key:value for key,value in old.items() if key != 'history'} == {key:value for key,value in new.items() if key != 'history'}
history_pin = new['history']
assert history_pin['path'] == 'source-history-gate.json'
assert sha(HERE / history_pin['path']) == history_pin['sha256']
assert (HERE / history_pin['path']).stat().st_size == history_pin['bytes']
assert not (HERE / 'verify-proofs.py').exists() and not (HERE / 'bound-data.json').exists()
archive(owner, 'proof-verifier-preparation-v2')
archive(audit, 'proof-verifier-v2-audit')
for filename in ['verify-proofs.py', 'bound-data.json']:
    (HERE / filename).write_bytes((owner / filename).read_bytes())
save('root-proof-verifier-v2-review.json', dict(
    status='ACCEPTED_WHOLE_REVIEWED_V2_FOR_STANDALONE_DUAL_MODE_EXECUTION',
    verifier_sha256=sha(owner / 'verify-proofs.py'), bound_data_sha256=sha(owner / 'bound-data.json'),
    independent_review_sha256=expected_review, root_whole_selected_source_lines_read=387,
    root_whole_previous_bound_data_lines_read=1119, exact_two_field_table_delta_checked=True,
    source_hard_stop=450, all_guard_families_retained=True,
    raw_source_headers_and_inventory_unchanged=True, original_v1_retained_unexecuted=True,
    metadata_revision_separately_reviewed=True, mathematical_sources_unchanged=True,
    standalone_normal_and_live_execution_accepted=True, execution_result_not_yet_claimed=True))
print('ACCEPTED and installed independently reviewed V2; standalone execution is now authorized.')
