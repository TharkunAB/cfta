import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

audit = Path('/tmp/mcfta-pair-request-admission-public-audit')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
source = HERE / (NAME + '.lean')
assert sha(source) == '103064aca3b5320b00e001823e6fd372ff51f1768b6dbf8683a8ed58148e5cfe'
assert len(source.read_bytes().splitlines()) == 157
readback = load(HERE / 'public-readback/pair-request-admission-full-readback.json')
head, = readback['heads']
short = 'completed_admitted'
checked = HERE / ('public-readback/pair-request-admission-' + short + '-public-type.txt')
printed = HERE / ('public-readback/pair-request-admission-' + short + '-printed-public-type.txt')
assert sha(checked) == 'd2c2d75fb35b20ac5327d57535140b5261a8360f5c9df3638353c4aaf0a6c9ee'
assert checked.read_bytes() == printed.read_bytes() and checked.stat().st_size == 32076
assert head['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
for filename, pin in readback['retained_slices'].items():
    path = HERE / 'public-readback' / filename
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256']
raw = HERE / 'pair-request-admission-public-1.log'
assert raw.stat().st_size == 2959024
assert sha(raw) == readback['log_sha256'] == '3118c4286d375adf21580fe264a84cab823506f046f04146dc1760c65177a725'
assert (HERE / 'pair-request-admission-strict-1.log').read_bytes() == b''
archive(audit, 'public-audit')
report = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT',
    observed_at=datetime.datetime.now().astimezone().isoformat(), source_sha256=sha(source), source_lines=157,
    public_heads=[head['head']], complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    root_read_complete_public_types=True, four_private_markers_and_all_helpers_absent_from_type=True,
    types_sha256={short: sha(checked)}, full_raw_sha256=sha(raw), actual_axioms_by_head={short: head['actual_axioms']},
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    root_printed_type_lexical_identity_verified=True, raw_type_byte_identity_by_head={short: True},
    root_printed_type_byte_identity_verified=True, independent_review='public-audit/review.json',
    independent_review_sha256=sha(audit / 'review.json'),
    complete_checked_type_lines=len(checked.read_bytes().splitlines()), complete_checked_type_bytes=32076,
    root_manual_read_scope='All checked public TYPE lines and157 ordinary source lines. Printed TYPE and complete BODY checked programmatically. No whole BODY manual read claim.')
true_scope = ['all_phase_pair_request_admission_derived', 'returned_canonical_request_admission_derived',
    'same_observed_run_and_full_after_state', 'genuine_initial_and_current_admission_explicit',
    'fixed_view_model_ranks_holds']
false_scope = ['execution_producer_claimed', 'final_stable_producer_claimed', 'native_covered_producer_claimed',
    'model_rebase_claimed', 'generated_root_composition_claimed', 'new_source_room_claimed',
    'word_ranges_claimed', 'public_pass_claimed', 'haskell_refinement_claimed', 'whole_goal_complete',
    'future_success_premise']
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
    output.write('\n## Complete public statement accepted\n\nStrict1 passes with a literal-empty log. The sole FULL1 passes.\nRoot and independent reviewers read the complete public TYPE.\nChecked and printed TYPE bytes match. Actual axioms are the three permitted standards.\nThe exact157-line module and one inverse Audit import are installed.\nThe aggregate Audit remains pending. The whole goal stays ACTIVE.\n')
print(json.dumps(dict(status='PASS', official_module=str(target), complete_type_lines=report['complete_checked_type_lines'],
    actual_jobs=2, failed_jobs=0, new_lean_lake_jobs=0)))
