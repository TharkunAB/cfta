import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

audit = Path('/tmp/mcfta-both-miss-native-covered-final-doc-audit')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
verification = load(HERE / 'verification.json')
preserved = load(HERE / 'preservation-final.json')
assert verification['status'] == preserved['status'] == 'PASS'
assert preserved['baseline_files'] == 102314 and preserved['unchanged_older_non_audit_sources'] == 3641
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
assert preserved['haskell_fix_registry_first_and_retained'] is True
assert verification['actual_jobs'] == 3 and verification['failed_jobs'] == 0
assert verification['audit_build_jobs'] == 3643 and verification['audit_dependencies'] == 75504
assert load(HERE / 'root-next-comparison-review.json')['status'] == 'SOURCE_ONLY_ROUTE_CLEAR'
archive(audit, 'final-doc-audit')
review = dict(status='ROOT_FINAL_DOCUMENT_REVIEW_CLEAR', proof=(HERE / 'proof-commit.txt').read_text().strip(),
    root_read_scope='Complete focused note and NEXT-TARGET, current update, FINDINGS repair index and update, source152/TYPE1294, normal/live reports and preservation scalar report. All nine original document inverses verified.',
    independent_review='final-doc-audit/review.json', independent_review_sha256=sha(audit / 'review.json'),
    haskell_repairs_added=0, haskell_repair_index_first=True,
    next_scope='Derive checked-state equality for the SAME supplied completed-hit H7 done. Initial Stable and actual published original/reverse key remain premises. A fresh exact declaration gate is required. Later H15 native/pair certificate lifts and generated-root resources stay separate.',
    whole_goal_complete=False, seal_or_network_publication_success_claimed=False)
save('root-final-doc-review.json', review)
publication = dict(status='ROOT_ACCEPTED', publication_scope='LOCAL_ONLY',
    network_publication='AUTHORIZED_PENDING_ROOT_PUSH', proof_commit=review['proof'],
    destination='git@github.com:TharkunAB/cfta.git', ref='refs/heads/formalize',
    root_and_independent_document_reviews='CLEAR', mandatory_seal_verification_required=True, whole_goal_complete=False)
save('publication-gate.json', publication)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Current handoff status\n\nProof commit `' + review['proof'] + '` is complete.\nThe exact nine document prefixes and focused note are written and reviewed.\nAll nine bound tools are installed. Normal and live standalone checks pass.\nThe complete checkpoint and baseline-preservation checks pass.\nFinal seal, local evidence commit and the authorized push remain pending at this gate.\n')
    output.write('\n## Goal turn outcome\n\nThis goal turn is PROGRESS. H26 derives native Covered\nthrough the SAME H13 BOTH-miss comparison and full returned state.\nRoot and independent reviews accept the exact public TYPE and actual evidence.\nBoth standalone verification modes passed before document writes.\nThe baseline preservation and all nine document inverses pass.\nThe next same-done completed-hit readback has a reviewed source-only route.\nThe whole formalization goal remains ACTIVE. Seal, local publication and authorized push follow this gate.\n')
print(json.dumps(dict(status='PASS', proof=review['proof'], publication_scope='LOCAL_ONLY',
    network_publication='AUTHORIZED_PENDING_ROOT_PUSH')))
