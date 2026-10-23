exec(compile(open('/tmp/mcfta-scan-node-counter-growth-root-common.py').read(), '/tmp/mcfta-scan-node-counter-growth-root-common.py', 'exec'))
import re
import sys
peer = Path(sys.argv[1])
checked_package(peer,sys.argv[2],sys.argv[3])
assert sha(peer / 'review.json') == sys.argv[4] and load(peer / 'review.json')['status'] == 'CLEAR'
source = Path('/tmp/mcfta-scan-node-counter-growth-body-v1.lean')
assert sha(source) == '7db9cd645899e31a3f04149e0ea8bd27f8e5c55c336aab872f8c286c04822cb7'
raw = source.read_bytes()
text = raw.decode()
assert len(raw.splitlines()) == 80 and len(raw.splitlines()) <= 140
assert load(HERE / 'root-declaration-gate.json')['body_authoring_authorized']
plan = HERE / 'declarations'
positions = []
for record in load(plan / 'insertion-map.json')['compiled_fragments']:
    fragment = (plan / record['file']).read_bytes()
    assert sha(plan / record['file']) == record['sha256']
    if record.get('remove_only_final_LF_before_attachment'):
        fragment = fragment[:-1]+record['future_body_attachment'].encode()
    assert raw.count(fragment) == 1
    positions.append(raw.index(fragment))
assert len(positions) == 6 and positions == sorted(positions) and positions[0] == 0
assert re.findall(r'(?m)^(def|theorem) (\w+)',text) == [('def','outcomeState'),('theorem','step_mono'),('theorem','execute_mono')]
assert not re.search(r'\b(?:private|sorry|axiom|unsafe|partial|set_option|termination_by|obtain|show|intro|let|by_cases)\b',text)
assert re.findall(r'(?m)^\s+have (\w+)',text) == ['pairGrowth','first']
assert text.count('cases observed :') == 2
assert text.count('ih next after') == text.count('induction fuel generalizing control state with') == 1
external = 'SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.step_mono'
assert text.count(external) == 1 and re.search(r'(?m)^        exact '+re.escape(external)+r' inner state$',text)
assert text.rstrip().endswith('end MicroCFTA.'+NAME)
archive(peer,'body-audit')
snapshot = HERE / 'root-body-v1.lean'
assert not snapshot.exists()
snapshot.write_bytes(raw)
save('root-body-gate.json',dict(status='ACCEPTED_COMPLETE_BODY_BEFORE_FIRST_COMPILER',
    module=NAME,body_source=snapshot.name,source_sha256=sha(snapshot),source_lines=80,
    root_complete_source_read=True,exact_contracts=6,exact_contract_lines=29,
    complete_public_types_context_and_24_scoped_types_read=True,
    all_10_equation_specializations_five_accessor_equations_and_generalized_IH_read=True,
    same_actual_state_all_five_outcomes=True,no_ID_split_or_counter_premise=True,
    sole_IH_call='ih next after',independent_review_sha256=sha(peer / 'review.json'),source_cap=140,
    below_target_without_padding_allowed=True,default_declaration_limits=True,all_linters=True,
    first_strict_authorized=True,full_or_official_install_authorized=False))
print('Accepted the complete unchanged 80-line body. First all-linter strict check authorized.')
