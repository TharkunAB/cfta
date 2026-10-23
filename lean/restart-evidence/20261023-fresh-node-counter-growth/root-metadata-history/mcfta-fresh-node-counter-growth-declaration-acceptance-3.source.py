exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import sys
owner_pins,owner_freeze,review_path,review_pins,review_freeze,review_sha=sys.argv[1:]
owner=Path('/tmp/mcfta-fresh-node-counter-growth-declaration-plan-v3')
review=Path(review_path)
checked_package(owner,owner_pins,owner_freeze)
checked_package(review,review_pins,review_freeze)
assert sha(review/'review.json')==review_sha and load(review/'review.json')['status']=='CLEAR'
old=HERE/'declaration-plan-v2'
contracts=load(owner/'contracts.json')
assert len(contracts)==10 and sum(len((owner/f).read_bytes().splitlines()) for f in contracts)==45
instance='[DecidableEq (EdgeKey Symbol Guard)]'
heads={'private-work.lean.txt':'work_mono','private-request.lean.txt':'request_mono',
       'public-build.lean.txt':'build_mono','public-many.lean.txt':'buildMany_mono','public-edges.lean.txt':'buildEdges_mono'}
for file in contracts:
    expected=(old/file).read_text()
    if file=='context.lean.txt':
        expected=expected.replace('variable '+instance+'\n','')
    elif file=='private-bind.lean.txt':
        assert expected.startswith('omit '+instance+' in\n')
        expected=expected[len('omit '+instance+' in\n'):]
    elif file in heads:
        token='theorem '+heads[file]
        assert expected.count(token)==1
        expected=expected.replace(token,token+' '+instance)
    assert (owner/file).read_text()==expected,file
for file in ['introduced-types.json','recursive-call-contracts.json','mutual-induction.json']:
    assert (owner/file).read_bytes()==(old/file).read_bytes()
assert load(HERE/'strict2.json')['exit_code']==0 and (HERE/'strict2.log').stat().st_size==267
archive(owner,'declaration-plan-v3')
archive(review,'declaration-v3-audit')
gate=load(HERE/'root-declaration-gate-v2.json')
gate.pop('private_bind_omit_prefix_complete_read')
gate.update(contracts_sha256=sha(owner/'contracts.json'),insertion_map_sha256=sha(owner/'insertion-map.json'),
    independent_review_sha256=review_sha,compiled_fragment_lines=45,root_whole_context_lines_read=8,
    root_whole_private_header_lines_read=18,contract_root='declaration-plan-v3',previous_gate='root-declaration-gate-v2.json',
    explicit_instance_heads=list(heads.values()),global_instance_declaration=False,omit_directives=0,
    root_all_five_explicit_instance_headers_read=True,public_requirements_and_conclusions_unchanged=True,
    strict2_warning_and_failed_metadata_selection_retained=True,compiler_activation_authorized=False)
save('root-declaration-gate-v3.json',gate)
for base,name in [('root-full-tool-scope-gate-v2.json','root-full-tool-scope-gate-v3.json'),
                  ('root-proof-verifier-scope-gate-v2.json','root-proof-verifier-scope-gate-v3.json')]:
    scoped=load(HERE/base)
    scoped.update(previous_scope_gate=base,declaration_gate='root-declaration-gate-v3.json',
        declaration_gate_sha256=sha(HERE/'root-declaration-gate-v3.json'),contract_root='declaration-plan-v3',
        compiled_fragment_lines=45,context_lines=8,private_header_lines=18,
        sole_declaration_delta='Replace the global instance and omit directive with explicit instances on the five theorems that use them.')
    save(name,scoped)
print('ACCEPTED exact explicit-instance declarations before V4 body; all previous declarations, warnings and metadata failure retained.')
