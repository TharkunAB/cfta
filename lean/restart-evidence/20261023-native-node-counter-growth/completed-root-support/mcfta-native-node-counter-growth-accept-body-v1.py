exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import re
import sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
review = Path('/tmp/mcfta-native-node-counter-growth-body-audit-v1')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review and load(review / 'review.json')['status'] == 'CLEAR'
source = HERE / 'variants/v1' / (NAME + '.lean')
text = source.read_text()
assert sha(source) == 'b43e0c75517bb57db8a062d45c2282c9117ce3944d5086d323318790a8fb9bec'
assert len(text.splitlines()) == 79
assert re.findall(r'\bhave\s+(\w+)', text) == ['growth', 'first']
assert re.findall(r'^\s*cases\s+(\w+)\s*:', text, re.M) == ['constructed', 'observed']
assert text.count('induction fuel generalizing code state with') == text.count('ih next after') == 1
assert not re.search(r'\b(?:private|def|let|obtain|show|intro|termination_by)\b', text)
for name, digest in load(HERE / 'declaration-plan/contracts.json').items():
    fragment = HERE / 'declaration-plan' / name
    assert sha(fragment) == digest
    header = fragment.read_text()
    assert text.count(header if name == 'context.lean.txt' else header.removesuffix('\n') + ' := by\n') == 1
archive(review, 'body-v1-audit')
save('root-body-gate-v1.json', dict(status='ACCEPTED_COMPLETE_BODY_BEFORE_STRICT', module=NAME,
    source=str(source.relative_to(HERE)), source_sha256=sha(source), source_lines=79,
    independent_review_sha256=expected_review, declaration_gate='root-declaration-gate.json',
    declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    root_complete_source_read=True, root_complete_source_lines_read=79,
    root_all_three_bodies_and_six_fragments_read=True, root_all_twelve_scoped_introduced_types_read=True,
    root_all_six_case_equation_types_read=True, root_complete_generalized_fuel_IH_read=True,
    private_helpers=[], public_heads=['step_mono', 'execute_mono', 'resume_mono'],
    haves=2, lets=0, obtains=0, induction=True, restricted_induction_call='ih next after',
    recursive_calls=0, termination_by_count=0,
    actual_pending_constructor_heap_and_actual_yielded_IH_state=True,
    no_public_validity_success_callback_or_final_counter_oracle=True,
    source_hard_stop=160, below_soft_target_without_padding=True,
    default_declaration_limits=True, all_linters=True, compiler_activation_authorized=True,
    goal_status='ACTIVE_INCOMPLETE'))
print('Accepted the complete 79-line body for its first strict check.')
