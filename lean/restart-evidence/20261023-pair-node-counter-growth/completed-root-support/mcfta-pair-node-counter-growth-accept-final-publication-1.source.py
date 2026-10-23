exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import datetime
import sys
peer = Path(sys.argv[1])
checked_package(peer,sys.argv[2],sys.argv[3])
assert sha(peer / 'review.json') == sys.argv[4]
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert proof == '39da661878d9e83362947f2621e6d1110dab6897'
assert git('rev-parse','HEAD').strip() == proof and git('rev-parse',proof+'^').strip() == START
assert not git('diff','--cached','--name-only').strip()
for mode,live in [('normal',False),('live',True)]:
    report = load(HERE / ('proof-evidence-'+mode+'.json'))
    assert report['status'] == 'PASS' and report['live'] is live
    assert report['actual_jobs'] == 3 and report['failed_jobs'] == report['new_lean_lake_jobs'] == 0
assert load(HERE / 'verification.json')['status'] == 'PASS'
preserved = load(HERE / 'preservation-final.json')
assert preserved['status'] == 'PASS' and preserved['baseline_files'] == 122017
assert preserved['unchanged_older_non_audit_sources'] == 3654
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
assert preserved['frozen_registry_count'] == 321 and preserved['frozen_entries'] == 1417
basis = Path('/tmp/mcfta-demand-node-counter-growth-authorized-push-1.source.py')
push_source = Path('/tmp/mcfta-pair-node-counter-growth-authorized-push.py')
assert push_source.read_bytes() == basis.read_bytes().replace(b'demand-node-counter-growth',b'pair-node-counter-growth')
archive(peer,'final-documents-audit')
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
with (HERE / 'current-progress.md').open('a') as stream:
    stream.write('\n## Actual saved-evidence and publication review\n\nUpdated: '+now+'.\n\n')
    stream.write('The unchanged source passed both standalone saved-evidence modes from cwd /. No new Lean or Lake job ran.\n')
    stream.write('The exact source and sole Audit import are committed at '+proof+'.\n')
    stream.write('All nine document updates retain the old bytes by exact prefix inverse. The focused note is added.\n')
    stream.write('FINDINGS keeps the external Haskell repair index first. No Haskell or package file changes.\n')
    stream.write('The first full preservation check passed for all 122017 baseline files and modes, 3654 older Lean sources, 298 Haskell files and 207 package files.\n')
    stream.write('The independent final documentation and actual preservation review is CLEAR.\n')
    stream.write('Final support collection, mandatory checkpoint replay before sealing, local publication and the authorized push remain pending at this record.\n')
    stream.write('The next mathematical target is the Scan node-counter bound, then its lift through H23. Fixed-source initial counter order and original global domain history remain separate.\n')
    stream.write('Earlier H23 conditional completion and language results remain proved. H6 remains strongest combined. The whole goal is ACTIVE and incomplete.\n')
save('publication-gate.json',dict(status='ROOT_ACCEPTED',proof_commit=proof,
    publication_scope='LOCAL_ONLY',network_publication='AUTHORIZED_PENDING_ROOT_PUSH',
    independent_review_sha256=sha(peer / 'review.json'),
    root_complete_current_update_focused_note_next_target_and_repair_index_read=True,
    root_actual_progress_addendum_read=True,root_all_old_text_inverse_and_baseline_preservation_checked=True,
    historical_cut_and_later_closing_receipts_retained_separately=True,
    all_actual_proof_and_metadata_evidence_retained=True,no_haskell_repair=True,whole_goal_complete=False,
    independent_review_authorship_clarification='Guard authored the selected closing and publication programs. Root bound the ten actual closing literals and authored the mathematical bodies and documents. The frozen peer phrase Root authored closing tools is imprecise. Reviewer independence and all checked bytes remain unchanged.',
    push_wrapper_literal_adaptation_only=True,push_wrapper_sha256=sha(push_source),
    next_actions='Archive support once. Seal with mandatory checkpoint replay at the final component count. Verify and publish locally. Then push the exact two commits to origin/formalize under standing explicit authorization.'))
print('Accepted final actual documentation and preservation review. Local publication and authorized push remain gated by support and seal.')
