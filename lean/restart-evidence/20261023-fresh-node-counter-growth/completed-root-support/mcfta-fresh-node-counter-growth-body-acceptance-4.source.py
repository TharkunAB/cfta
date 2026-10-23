exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import re,sys
expected_pins,expected_freeze,expected_review=sys.argv[1:]
package=Path('/tmp/mcfta-fresh-node-counter-growth-body-v4-audit')
checked_package(package,expected_pins,expected_freeze)
assert sha(package/'review.json')==expected_review and load(package/'review.json')['status']=='CLEAR'
source=HERE/'variants/v4'/(NAME+'.lean')
assert sha(source)=='2ce7e811918f8dbf189bd9d1ea4cc2a9bef35d80f42dc9b750f998b68b866ca8'
text=source.read_text()
assert len(text.splitlines())==117
assert load(HERE/'root-declaration-gate-v3.json')['body_authoring_authorized']
plan=HERE/'declaration-plan-v3'
for name,record in zip(load(plan/'contracts.json'),load(plan/'insertion-map.json')['compiled_fragments'],strict=True):
    fragment=(plan/name).read_text()
    if 'future_body_attachment' in record:
        fragment=fragment[:-1]+record['future_body_attachment']
    assert text.count(fragment)==1,name
assert text.count('[DecidableEq (EdgeKey Symbol Guard)]')==5
assert 'omit ' not in text and 'variable [DecidableEq' not in text
assert re.findall(r'(?m)^\s*have\s+(\w+)',text)==['reserved','preserved']
assert re.findall(r'(?m)^\s*let\s+(\w+)',text)==['callback']
assert text.count('termination_by sizeOf expression')==3 and 'set_option' not in text
archive(package,'body-v4-audit')
gate=load(HERE/'root-body-gate-v3.json')
gate.pop('private_unused_instance_omitted')
gate.update(source=str(source.relative_to(HERE)),source_sha256=sha(source),source_lines=117,
    independent_review_sha256=expected_review,declaration_gate='root-declaration-gate-v3.json',
    declaration_gate_sha256=sha(HERE/'root-declaration-gate-v3.json'),root_complete_source_lines_read=117,
    root_complete_source_read=True,private_bind_has_no_unused_instance=True,all_five_instance_headers_read=True,
    all_six_body_texts_unchanged=True,strict2_warning_and_failed_metadata_selection_retained=True)
save('root-body-gate-v4.json',gate)
print('ACCEPTED whole117-line V4 and independent review before strict3; all six proof bodies unchanged.')
