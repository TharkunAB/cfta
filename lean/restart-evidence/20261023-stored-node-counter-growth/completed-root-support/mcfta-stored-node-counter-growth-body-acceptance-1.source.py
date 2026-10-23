exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
import re
import sys
review = Path('/tmp/mcfta-stored-node-counter-growth-body-v1-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review
assert load(review / 'review.json')['status'] == 'CLEAR'
source = HERE / 'variants/v1' / (NAME + '.lean')
assert sha(source) == '2dc66e6e7cc728b051a65d622f6aab9bd236ac485b90eb4c1f60650fc438d16a'
text = source.read_text()
assert len(text.splitlines()) == 82
assert re.findall(r'\bhave\s+(\w+)', text) == ['reserved']
assert not re.search(r'\b(?:let|obtain|show|induction|termination_by)\b', text)
assert sha(HERE / 'root-declaration-gate.json') == '79caf4af3f1df76e9cc916cf4ed552df9326966bb8f42307e84ba2eb21134696'
plan = HERE / 'declaration-plan'
for name, digest in load(plan / 'contracts.json').items():
    assert sha(plan / name) == digest
    fragment = (plan / name).read_text()
    if name != 'context.lean.txt':
        fragment = fragment.rstrip('\n') + ' := by\n'
    assert text.count(fragment) == 1, name
archive(review, 'body-v1-audit')
save('root-body-gate-v1.json', dict(status='ACCEPTED_COMPLETE_BODY_BEFORE_STRICT', module=NAME,
    source=str(source.relative_to(HERE)), source_sha256=sha(source), source_lines=82,
    independent_review_sha256=expected_review, declaration_gate='root-declaration-gate.json',
    declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    root_complete_source_read=True, root_complete_source_lines_read=82,
    root_all_six_bodies_and_eight_fragments_read=True, root_all_seven_scoped_introduced_types_read=True,
    private_helpers=['bind_mono','callback_mono','request_mono'],
    public_heads=['execute_mono','unfold_mono','maybeMu_mono'], haves=1, lets=0, obtains=0,
    induction=False, recursive_calls=0, termination_by_count=0,
    concrete_callback_bound_derived_from_public_H33_and_Work=True,
    actual_repaired_pending_included=True, same_literal_probes_and_request_and_returned_states=True,
    no_new_public_oracle_or_success_or_validity_requirement=True,
    source_hard_stop=160, below_soft_target_without_padding=True,
    default_declaration_limits=True, all_linters=True, compiler_activation_authorized=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED complete82-line source and independent body review; strict compilation authorized.')
