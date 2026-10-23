import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

audit = Path('/tmp/mcfta-both-miss-native-covered-public-audit')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
source = HERE / (NAME + '.lean')
assert sha(source) == '09e8927b6e9a98fa39704567fd6b48164dfc2a30d45ea389e0d8e4a36d71116b'
assert len(source.read_bytes().splitlines()) == 152
readback = load(HERE / 'public-readback/both-miss-native-covered-full-readback.json')
head, = readback['heads']
short = 'both_miss_complete'
checked = HERE / ('public-readback/both-miss-native-covered-' + short + '-public-type.txt')
printed = HERE / ('public-readback/both-miss-native-covered-' + short + '-printed-public-type.txt')
assert sha(checked) == '8db732881105e579a8efc96244810eaea5d33473095023fb6445347c63082903'
assert checked.read_bytes() == printed.read_bytes() and checked.stat().st_size == 138240
assert len(checked.read_bytes().splitlines()) == 1294
assert checked.read_bytes().count(b'\n') == 1293 and not checked.read_bytes().endswith(b'\n')
assert head['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
for filename, pin in readback['retained_slices'].items():
    path = HERE / 'public-readback' / filename
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256']
raw = HERE / 'both-miss-native-covered-public-1.log'
assert raw.stat().st_size == 3495715
assert sha(raw) == readback['log_sha256'] == 'e7b8013f2f8e898ca6177cafb96ce48bc8ffeafee3e6f9e66ec02e2f112ae4d0'
assert (HERE / 'both-miss-native-covered-strict-1.log').read_bytes() == b''
archive(audit, 'public-audit')
report = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    observed_at=datetime.datetime.now().astimezone().isoformat(), source_sha256=sha(source), source_lines=152,
    public_heads=[head['head']], complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    root_read_complete_public_types=True, four_private_markers_and_all_helpers_absent_from_type=True,
    types_sha256={short: sha(checked)}, full_raw_sha256=sha(raw), actual_axioms_by_head={short: head['actual_axioms']},
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    root_printed_type_lexical_identity_verified=True, raw_type_byte_identity_by_head={short: True},
    root_printed_type_byte_identity_verified=True, independent_review='public-audit/review.json',
    independent_review_sha256=sha(audit / 'review.json'),
    complete_checked_type_lines=1294, complete_checked_type_bytes=138240,
    root_manual_read_scope='All1294 raw checked TYPE lines in four complete untruncated ranges and all152 ordinary source lines. Printed TYPE and whole BODY checked programmatically. No whole BODY manual read claim.')
true_scope = ['fixed_source_model_ranked_holds', 'genuine_initial_native_covered_and_parent_admissions',
    'all_H13_outputs_preserved', 'same_H13_native_receipt_and_full_after',
    'literal_branch_admission_and_edge_body_certificate', 'native_covered_derived']
false_scope = ['pair_admission_output', 'generated_root_admission', 'model_rebase_producer',
    'new_resource_room_producer', 'mu_full_pass', 'haskell_refinement', 'practical_width',
    'convergence', 'whole_goal_complete', 'future_success_or_final_covered_premise']
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
    output.write('\n## Complete public statement accepted\n\nStrict1 passes with a literal-empty log. The sole FULL1 passes.\nRoot and independent reviewers read all1294 public TYPE lines.\nChecked and printed TYPE bytes match. Actual axioms are the three permitted standards.\nThe exact152-line module and one inverse Audit import are installed.\nThe aggregate Audit remains pending. The whole goal stays ACTIVE.\n')
print(json.dumps(dict(status='PASS', official_module=str(target), complete_type_lines=1294,
    actual_jobs=2, failed_jobs=0, new_lean_lake_jobs=0)))
