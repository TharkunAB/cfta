import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

audit = Path('/tmp/mcfta-completed-hit-readback-public-audit')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
source = HERE / (NAME + '.lean')
assert sha(source) == '4bf1df4098cbc276613106c45d1279a1ce156bb3832b6c813874a3c568522c15'
assert len(source.read_bytes().splitlines()) == 147
readback = load(HERE / 'public-readback/completed-hit-readback-full-readback.json')
head, = readback['heads']
short = 'completed_hit_checked'
checked = HERE / ('public-readback/completed-hit-readback-' + short + '-public-type.txt')
printed = HERE / ('public-readback/completed-hit-readback-' + short + '-printed-public-type.txt')
assert sha(checked) == 'd8ca786b563e5633addf1c28948e492a7cf30a8ca872da41611652b7b015078f'
assert checked.read_bytes() == printed.read_bytes() and checked.stat().st_size == 7032
assert len(checked.read_bytes().splitlines()) == 102
assert checked.read_bytes().count(b'\n') == 101 and not checked.read_bytes().endswith(b'\n')
assert head['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
for filename, pin in readback['retained_slices'].items():
    path = HERE / 'public-readback' / filename
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256']
raw = HERE / 'completed-hit-readback-public-1.log'
assert raw.stat().st_size == 2814841
assert sha(raw) == readback['log_sha256'] == 'e28b47206fc20e1d85f6619a8e27c3856f049f45811fe87077493a03bf8d938d'
assert (HERE / 'completed-hit-readback-strict-1.log').read_bytes() == b''
archive(audit, 'public-audit')
report = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    observed_at=datetime.datetime.now().astimezone().isoformat(), source_sha256=sha(source), source_lines=147,
    public_heads=[head['head']], complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    root_read_complete_public_types=True, four_private_markers_and_all_helpers_absent_from_type=True,
    types_sha256={short: sha(checked)}, full_raw_sha256=sha(raw), actual_axioms_by_head={short: head['actual_axioms']},
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    root_printed_type_lexical_identity_verified=True, raw_type_byte_identity_by_head={short: True},
    root_printed_type_byte_identity_verified=True, independent_review='public-audit/review.json',
    independent_review_sha256=sha(audit / 'review.json'),
    complete_checked_type_lines=102, complete_checked_type_bytes=7032,
    root_manual_read_scope='All102 raw checked TYPE lines and all147 ordinary source lines. Printed TYPE and whole BODY checked programmatically. No whole BODY manual read claim.')
true_scope = ['fixed_semantic_view_model_ranked_holds', 'genuine_initial_stable_and_published_key',
    'same_supplied_done_fuel_result_and_full_after', 'canonical_reverse_direction_derived',
    'captured_payload_not_identified_with_requested_pair', 'only_checked_state_equality']
false_scope = ['new_execution_producer', 'native_covered_output', 'pair_admission_output',
    'second_completion_or_crossfuel_uniqueness', 'generated_root_admission', 'model_rebase_producer',
    'new_resource_room_producer', 'mu_full_pass', 'haskell_refinement', 'practical_width',
    'convergence', 'whole_goal_complete', 'final_checked_equality_premise']
report.update({key: True for key in true_scope})
report.update({key: False for key in false_scope})
save('root-full-review.json', report)
save('root-full-review-scope.json', dict(required_true=true_scope, required_false=false_scope))
target = ROOT / 'lean/MicroCFTA' / (NAME + '.lean')
aggregate = ROOT / 'lean/MicroCFTA/Audit.lean'
original = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert not target.exists() and aggregate.read_bytes() == original
addition = ('import MicroCFTA.' + NAME + '\n').encode()
assert addition not in original
offset = original.index(b'/-!')
target.write_bytes(source.read_bytes())
aggregate.write_bytes(original[:offset] + addition + original[offset:])
assert aggregate.read_bytes().replace(addition, b'', 1) == original
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Complete public statement accepted\n\nStrict1 passes with a literal-empty log. The sole FULL1 passes.\nRoot and independent reviewers read all102 public TYPE lines.\nChecked and printed TYPE bytes match. Actual axioms are the three permitted standards.\nThe exact147-line module and one inverse Audit import are installed.\nThe aggregate Audit remains pending. The whole goal stays ACTIVE.\n')
print(json.dumps(dict(status='PASS', official_module=str(target), complete_type_lines=102,
    actual_jobs=2, failed_jobs=0, new_lean_lake_jobs=0)))
