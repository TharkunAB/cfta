exec(compile(open('/tmp/mcfta-scan-node-counter-growth-root-common.py').read(), 'root-common.py', 'exec'))
import datetime

peer = Path('/tmp/mcfta-scan-node-counter-growth-final-documents-review')
checked_package(peer, '01e9c35ac83292a7b3310b53105b7a6588e54f9f58c069905acfb655627fdfcd',
                'c8542b94e29e4d9c519cdcb6772d07688af4b01f2724b7468a875f51a7e431b6')
assert sha(peer / 'review.json') == '657d874bb7e38118733114e9c2c8c35322dd9746e487f2e76922d91a113abcfe'
review = load(peer / 'review.json')
assert review['status'] == 'CLEAR' and not review['blockers']
proof = '27cebaf220e74265207cef19212d40fb08ece98f'
assert git('rev-parse', 'HEAD').strip() == proof == (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD^').strip() == START
assert set(git('diff-tree', '--no-commit-id', '--name-only', '-r', proof).splitlines()) == {
    'lean/MicroCFTA/' + NAME + '.lean', 'lean/MicroCFTA/Audit.lean'}
assert sha(ROOT / ('lean/MicroCFTA/' + NAME + '.lean')) == review['source_sha256']
assert review['source_lines'] == 80
for name in ['current-update.md', 'proof-evidence-normal.json', 'proof-evidence-live.json',
             'verification.json', 'preservation-final.json']:
    assert (peer / 'inspected' / name).read_bytes() == (HERE / name).read_bytes()
assert (peer / 'inspected/notes-current-scan-node-counter-growth.md').read_bytes() == (
    ROOT / 'lean/notes-current-scan-node-counter-growth.md').read_bytes()
inverse = load(peer / 'document-byte-inverses.json')
assert inverse['all9_exact'] and inverse['update_lines'] == 38
for item in inverse['documents']:
    assert sha(ROOT / item['path']) == item['current_sha256'] and item['exact_LF_inverse']
assert len(inverse['documents']) == 9
for mode in ['normal', 'live']:
    assert load(HERE / ('proof-evidence-' + mode + '.json'))['status'] == 'PASS'
assert load(HERE / 'verification.json')['archived_components'] == 35
assert sha(peer / 'ownership-clarification.json') == '09ba82a3c76b113478bd6036cd5e9cfc2859bb9222f36958d4978ad514a586ba'
archive(peer, 'final-documents-audit')
save('root-final-documents-review.json', {
    'status': 'ACCEPTED_ACTUAL_DOCUMENTS_PROOF_AND_FIRST_CHECKPOINT',
    'proof_commit': proof, 'independent_review_sha256': sha(peer / 'review.json'),
    'root_whole_review_focused_note_update_and_ownership_clarification_read': True,
    'all_nine_document_byte_inverses': True, 'haskell_repair_index_first': True,
    'current_update_lines': 38, 'previous_39_line_cue_corrected': True,
    'ownership': {'templates_and_selected_adapters': 'Required', 'mathematical_body': 'Root',
                  'independent_reviewer': 'Arity'},
    'prior_frozen_reviews_unchanged': True,
    'first_checkpoint_components': 35, 'final_seal_must_refresh_checkpoint': True,
    'seal_local_publication_and_push_not_yet_claimed': True,
    'formalization_complete': False})
save('publication-gate.json', {
    'status': 'ROOT_ACCEPTED', 'publication_scope': 'LOCAL_ONLY',
    'network_publication': 'AUTHORIZED_PENDING_ROOT_PUSH', 'proof_commit': proof,
    'final_document_review': sha(HERE / 'root-final-documents-review.json'),
    'required_runtime_gate': 'Final seal must rerun the checkpoint after support capture.',
    'future_seal_or_push_success_claimed': False})
with (HERE / 'current-progress.md').open('a') as out:
    out.write('\n## Actual final document and proof checkpoint\n\nUpdated: ' +
              datetime.datetime.now(datetime.timezone.utc).isoformat() + '.\n\n')
    out.write('Both standalone proof evidence modes passed. Proof commit: ' + proof + '.\n')
    out.write('The nine document updates and focused note are written and independently reviewed.\n')
    out.write('Each exact LF inverse recovers the prior document. The Haskell repair index remains first.\n')
    out.write('The first checkpoint passed at 35 archived components. This is a historical cut.\n')
    out.write('The final seal must rerun the checkpoint after final review and support capture.\n')
    out.write('The update has 38 lines. The earlier 39-line review cue was incorrect.\n')
    out.write('The additive ownership clarification preserves the two prior frozen reviews.\n')
    out.write('Final seal, local evidence publication and authorized push remain pending.\n')
    out.write('H6 remains the strongest combined theorem. The whole formalization is incomplete.\n')
print('PASS: actual final documents and first checkpoint accepted; publication remains gated by the final seal.')
