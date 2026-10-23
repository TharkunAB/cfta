exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
owner = Path('/tmp/mcfta-stored-node-counter-growth-full-scope-plan')
review = Path('/tmp/mcfta-stored-node-counter-growth-full-scope-audit')
checked_package(owner, '27b38b746c3c4ae56752a848d7ced8fa7093fc29fd808ad027b184706ffda5ef', '2dd1f1ac1034d4abf80846a8aa591025cf56fdff08ec9941ede4bc2985e52b31')
checked_package(review, '7a26b74e4fe52dbb39af77f3725919fcaa3914875945dcd4422a1beaebcedf3f', '07b155f3a9f2865b6319efbfb427df13b554ba281aed2a7f6df242d1d9421070')
assert sha(review / 'review.json') == '23c9c9dc246d5b71f185af4aca0f6416b65d607108965fcda43ef79b1b7570bf'
assert load(review / 'review.json')['status'] == 'CLEAR'
early = HERE / (NAME + '.lean')
assert early.read_bytes() == (HERE / 'strict1.source.lean').read_bytes()
assert sha(early) == '2dc66e6e7cc728b051a65d622f6aab9bd236ac485b90eb4c1f60650fc438d16a'
retained = HERE / 'history-drafts/pre-materializer' / (NAME + '.lean.txt')
retained.parent.mkdir(parents=True)
assert not retained.exists()
early.rename(retained)
save('canonical-preparation-history.json', dict(status='EARLY_EVIDENCE_COPY_RETAINED_BEFORE_MATERIALIZER',
    reason='Strict selection copied the canonical source before the reviewed materializer, which requires a new output path.',
    retained_copy=str(retained.relative_to(HERE)), sha256=sha(retained),
    original_metadata_receipt='mcfta-stored-node-counter-growth-strict-selection-1',
    no_guard_changed=True, no_Lean_source_changed=True, no_proof_job_repeated=True,
    materializer_canonical_output_now_absent=not early.exists()))
archive(owner, 'full-scope-plan')
archive(review, 'full-scope-audit')
save('root-full-scope-gate.json', dict(status='ACCEPTED_FULL_TOOL_SCOPE_BEFORE_SELECTED_AUTHORSHIP',
    root_whole_plan_lines_read=26, root_whole_input_map_and_schema_adapters_read=True,
    root_whole_207_line_basis_previously_read_and_current_identity_checked=True,
    root_whole_materializer_83_line_basis_reread=True,
    independent_review_sha256=sha(review / 'review.json'), compiled_contracts=8,
    compiled_contract_lines=39, context_lines=9, private_header_lines=17, public_header_lines=12,
    local_fragment_lines=1, public_heads=['execute_mono','unfold_mono','maybeMu_mono'],
    private_helpers=['bind_mono','callback_mono','request_mono'], target_source_lines=[207,215],
    whole_selected_tools_hard_stop=220, materializer_cli_arguments=7, diagnostic_tail_lines=20,
    all_generic_guard_families_retained=True, canonical_nonoverwrite_guard_retained=True,
    early_copy_retained_as_history_not_discarded=True, selected_tools_authoring_authorized=True,
    materializer_FULL_reader_activation_authorized=False, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED FULL tooling scope; early canonical copy retained as history, nonoverwrite guard unchanged.')
