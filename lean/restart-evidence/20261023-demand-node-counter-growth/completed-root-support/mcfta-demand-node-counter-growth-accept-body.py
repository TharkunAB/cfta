exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import re
import sys

expected_pins, expected_freeze, expected_review = sys.argv[1:]
review = Path('/tmp/mcfta-demand-node-counter-growth-body-v1-review')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review and load(review / 'review.json')['status'] == 'CLEAR'
source = HERE / 'variants/v1' / (NAME + '.lean')
text = source.read_text()
assert sha(source) == 'c94db7eee4e7aa54d00f30ed4703301e5b4b5cefb106c1c619cc95994d3676f0'
assert len(text.splitlines()) == 80
assert re.findall(r'\bhave\s+(\w+)', text) == ['nativeGrowth', 'first']
assert re.findall(r'^\s*cases\s+(\w+)\s*:', text, re.M) == ['observed']
assert text.count('induction fuel generalizing control state with') == text.count('ih next after') == 1
assert re.findall(r'^private theorem (\w+)', text, re.M) == ['lift_native']
assert not re.search(r'\b(?:def|let|obtain|show|intro|termination_by)\b', text)
assert text.count('SourceRecursiveIntersectionNativeNodeCounterGrowth.step_mono') == 1
for name, digest in load(HERE / 'declaration-plan/contracts.json').items():
    fragment = HERE / 'declaration-plan' / name
    assert sha(fragment) == digest
    header = fragment.read_text()
    assert text.count(header if name == 'context.lean.txt' else header.removesuffix('\n') + ' := by\n') == 1
archive(review, 'body-v1-audit')
save('root-body-gate-v1.json', dict(status='ACCEPTED_COMPLETE_BODY_BEFORE_STRICT', module=NAME,
    source=str(source.relative_to(HERE)), source_sha256=sha(source), source_lines=80,
    independent_review_sha256=expected_review, declaration_gate='root-declaration-gate.json',
    declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    root_complete_source_read=True, root_complete_source_lines_read=80,
    root_all_four_bodies_and_seven_fragments_read=True, root_all_ten_scoped_introduced_types_read=True,
    root_all_five_case_equation_types_read=True, root_complete_generalized_fuel_IH_read=True,
    private_helpers=['lift_native'], public_heads=['step_mono', 'execute_mono', 'resume_mono'],
    haves=2, lets=0, obtains=0, induction=True, restricted_induction_call='ih next after',
    recursive_calls=0, termination_by_count=0,
    actual_wrapped_native_heap_and_actual_yielded_IH_state=True,
    all_five_checked_outcome_tags=True, no_public_validity_success_callback_or_final_counter_oracle=True,
    source_hard_stop=160, below_soft_target_without_padding=True,
    default_declaration_limits=True, all_linters=True, compiler_activation_authorized=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the complete 80-line body for its first strict check.')
