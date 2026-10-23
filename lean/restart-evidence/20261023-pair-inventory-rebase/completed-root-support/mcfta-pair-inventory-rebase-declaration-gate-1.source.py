exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-pair-inventory-rebase-declaration-plan')
review = Path('/tmp/mcfta-pair-inventory-rebase-declaration-audit')
checked_package(owner, 'b33878247c934c5d77dc872725137a389cfa76d242bf81f31ce5d6e110814a70', '261929ad45b3410c10c2614c5d2dc939331b49ff63d37627213a48d0c5f3c51a')
checked_package(review, 'b70bd852c58d341759c7e8dce25c647f48fa40583526fc8c9ca42fa3c3706637', '5515a9cfbeb51e9bafa352029464de9efbfb644fbe5dd6e8ab9f8b186ee29f45')
assert sha(review / 'review.json') == '66c77a2f0dc7beda66d490e7087cded2d0437abdf6de2cf1241093efbadddaa7'
assert load(review / 'review.json')['status'] == 'CLEAR'
assert sha(owner / 'contracts.json') == 'f02f56dc5171be6bb5156604b91d4d9f843fbcad42d898955a38c2426c8b4640'
assert sha(owner / 'insertion-map.json') == '9e27cf277e142a3128f484efbb77e8b6b8b39034377b15cf9d2283206df7f161'
assert git('rev-parse', 'HEAD').strip() == START
assert load(HERE / 'previous-local-checkpoint/mcfta-rebuild-admission-remote-publication.json')['checkpoint'] == START
archive(owner, 'declaration-plan')
archive(review, 'declaration-audit')
save('root-declaration-gate.json', dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    module=NAME, public_heads=['rebase'], contracts_sha256=sha(owner / 'contracts.json'),
    insertion_map_sha256=sha(owner / 'insertion-map.json'), independent_review_sha256=sha(review / 'review.json'),
    root_whole_context_lines_read=18, root_whole_public_header_lines_read=37,
    root_all_public_lets_and_introduced_field_types_read=True,
    root_all_local_have_let_obtain_and_lambda_types_read=True,
    compiled_fragments=6, compiled_fragment_lines=61, public_let_occurrences=3,
    body_lets=1, body_haves=2, body_obtains=1, obtain_fields=5,
    helpers=0, induction=False, agreement_derived_not_assumed=True,
    same_full_wrapper=True, new_execution_or_resources_claimed=False,
    source_target=[80,120], source_estimate=[85,110], whole_source_hard_stop=180,
    default_declaration_limits=True, all_linters=True,
    prior_checkpoint_pushed_and_remote_verified=START, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED all six exact declarations and introduced types before any body; prior checkpoint is pushed.')
