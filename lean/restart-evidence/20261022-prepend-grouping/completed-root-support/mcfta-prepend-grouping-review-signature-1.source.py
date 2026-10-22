import datetime
import hashlib
import json
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-prepend-grouping'
plan = here / 'signature-plan'
audit = here / 'signature-audit'
expected_review = sys.argv[1]
assert hashlib.sha256((audit / 'review.md').read_bytes()).hexdigest() == expected_review
pins = json.loads((plan / 'pins.json').read_text())
assert len(pins) == 44
for name, pin in pins.items():
    raw = (plan / name).read_bytes()
    assert len(raw) == pin['bytes']
    assert hashlib.sha256(raw).hexdigest() == pin['sha256']
index = json.loads((plan / 'source-index.json').read_text())
assert len(index['sources']) == 8
cuts = 0
for source in index['sources']:
    raw = Path(source['path']).read_bytes()
    assert raw == (plan / source['snapshot']).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == source['sha256']
    for cut in source['reviewed_ranges']:
        excerpt = b''.join(raw.splitlines(keepends=True)[cut['start']-1:cut['end']])
        assert excerpt == (plan / cut['excerpt']).read_bytes()
        assert len(excerpt) == cut['bytes']
        assert hashlib.sha256(excerpt).hexdigest() == cut['sha256']
        cuts += 1
assert cuts == 19
order = json.loads((plan / 'declaration-order.json').read_text())
assert order['definitions'] == ['insertWith', 'fromRows', 'reverseTable']
assert order['theorems'] == ['pair_fold', 'reverse_insert_singleton', 'reverse_fold',
    'reverse_fromRows', 'iteration_reverse', 'iteration_permutation']
assert order['private_declarations'] == [] and order['hard_stop_lines'] == 240
assert order['local_induction_statements'] == ['local-induction.lean.txt']
declarations = (plan / 'declarations.lean.txt').read_bytes()
assert hashlib.sha256(declarations).hexdigest() == 'c903f09c4f52b0db58dd5c94dbb85e765d5d84905666bc4f9216f567c16c333f'
assert len(declarations.splitlines()) == 49
assert not (root / 'lean/MicroCFTA/SourceCurrentPrependGrouping.lean').exists()
assert not list(here.glob('prepend-grouping-*.source.lean'))
assert (here / 'starting-head.txt').read_text().strip() == 'd0cf685f461430a7c608ceb3b76da0fe568e4d84'
record = dict(status='ROOT_DECLARATION_REVIEW_CLEAR',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_pins=len(pins), live_sources=8, live_cuts=cuts,
    root_read_complete_49_line_declaration_inventory=True,
    root_read_all_definition_equations_and_local_induction=True,
    root_read_whole_190_line_existing_grouping_and_all_19_cuts=True,
    independent_review='signature-audit/review.md', independent_review_sha256=expected_review,
    definitions=order['definitions'], public_theorems=order['theorems'],
    private_helpers=[], target_lines=order['target_lines'], hard_stop_lines=240,
    retains_absence_and_present_empty_buckets=True, reverses_arbitrary_initial_table=True,
    retains_duplicates_and_literal_iteration_keys_and_order=True,
    generic_key_later_instantiated_with_symbol_only=True,
    old_modules_unchanged_required=True, hash_map_refinement_claimed=False,
    stateful_group_consumer_claimed=False, mathematical_body_authorized=True,
    compiler_authorized=False, whole_source_review_required_before_checks=True,
    whole_goal_complete=False)
target = here / 'root-declaration-review.json'
assert not target.exists()
target.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(dict(status='PASS', pins=44, sources=8, cuts=19, definitions=3,
    public_theorems=6, body_authorized=True, compiler_authorized=False)))
