exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import re, sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
package = Path('/tmp/mcfta-fresh-node-counter-growth-body-v3-audit')
checked_package(package, expected_pins, expected_freeze)
assert sha(package / 'review.json') == expected_review and load(package / 'review.json')['status'] == 'CLEAR'
source = HERE / 'variants/v3' / (NAME + '.lean')
assert sha(source) == '464dbcf3adbb832a6507510f2497c476b6f3f0b435358068e0e2621eb183f693'
text = source.read_text()
assert len(text.splitlines()) == 119
assert load(HERE / 'root-declaration-gate-v2.json')['body_authoring_authorized']
plan = HERE / 'declaration-plan-v2'
contracts = load(plan / 'contracts.json')
layout = load(plan / 'insertion-map.json')['compiled_fragments']
for name, record in zip(contracts, layout, strict=True):
    fragment = (plan / name).read_text()
    if 'future_body_attachment' in record:
        fragment = fragment[:-1] + record['future_body_attachment']
    assert text.count(fragment) == 1, name
assert re.findall(r'(?m)^\s*have\s+(\w+)', text) == ['reserved','preserved']
assert re.findall(r'(?m)^\s*let\s+(\w+)', text) == ['callback']
assert text.count('termination_by sizeOf expression') == 3
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|partial|obtain|suffices|haveI|letI|by_cases|induction)\b|set_option',text)
archive(package,'body-v3-audit')
save('root-body-gate-v3.json',dict(status='ACCEPTED_COMPLETE_BODY_BEFORE_STRICT',module=NAME,
    source=str(source.relative_to(HERE)),source_sha256=sha(source),source_lines=119,
    independent_review_sha256=expected_review,declaration_gate='root-declaration-gate-v2.json',
    declaration_gate_sha256=sha(HERE/'root-declaration-gate-v2.json'),
    root_complete_source_read=True,root_complete_source_lines_read=119,root_all_six_bodies_read=True,
    root_all_ten_fragments_read=True,root_all_23_scoped_types_and_seven_restricted_calls_read=True,
    private_helpers=['work_mono','bind_mono','request_mono'],public_heads=['build_mono','buildMany_mono','buildEdges_mono'],
    haves=2,lets=1,obtains=0,termination_by_count=3,actual_repaired_pending_included=True,
    source_hard_stop=180,below_soft_target_without_padding=True,
    private_unused_instance_omitted=True,actual_state_arguments_and_base_equations_explicit=True,
    strict1_failed_source_and_diagnostics_retained=True,default_declaration_limits=True,all_linters=True,
    compiler_activation_authorized=True,goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED complete V3 source and independent review before strict2. All prior sources and strict1 retained.')
