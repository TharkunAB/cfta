import runpy
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

package = Path('/tmp/mcfta-comparison-native-covered-route-audit')
entries = checked_package(package,
    'c54b05a9aa8ea07f0c02c60e520b6a910f0516f069091fc16dddf88a208d5370',
    '09c393b54f0e35dbf30fc6fb661e28bc1e3deea64e0f3196a5c4e2ca8f18967b')
assert sha(package / 'review.json') == '88fa39288dee2980d08770fef3971513cbcbe7313fece5255bbbf17154c728f1'
review = load(package / 'review.json')
assert review['status'] == 'SOURCE_ONLY_CLEAR'
assert review['all_H15_outputs_retained'] == 12 and review['H15_invocations_proposed'] == 1
assert review['new_global_helpers_proposed'] == 0 and not review['new_induction_proposed']
assert review['arbitrary_initialDomains_Valid_globalTrace_Room_retained']
assert review['physical_trace_from_prefixes_not_raw_erasure'] and review['scope_clarification_emptyDomain_only']
archive(package, 'route-audit')
save('root-route-review.json', dict(status='ROOT_SOURCE_ONLY_CLEAR', review_sha256=sha(package / 'review.json'),
    root_read_scope='Whole H15/H26/H27 source; complete Resources, PrefixReceipt, Admits and physical/admission certificate definitions, public miss readback and Trace.covered; whole route review MD and JSON.',
    declaration_or_body_authorized=False, compiler_jobs=0, whole_goal_complete=False))
print(json.dumps(dict(status='PASS', archived_files=len(entries), declaration_or_body_authorized=False)))
