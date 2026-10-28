from pathlib import Path
from hashlib import sha256
from datetime import datetime
import json
import shutil

R=Path('/home/tritlo/Code/mcfta')
A=Path('/tmp/mcfta-native-partial-output-20261028')
O=A/'recursive-model-review'
records=[]
for name in ['program-hole-origins-strict-1','program-hole-origins-strict-2',
             'type-origin-boundary-strict-1','type-origin-boundary-strict-2',
             'native-partial-output-strict-1','native-partial-output-strict-2','native-partial-output-strict-3',
             'history-partial-output-strict-1','initial-partial-output-strict-1','initial-partial-output-strict-2',
             'selected-value-strict-1']:
    origin=A/name
    report=json.loads((origin/'report.json').read_text())
    paths=[origin/'report.json',origin/'raw.log',*sorted((origin/'MicroCFTA').rglob('*.lean'))]
    copies=[]
    for path in paths:
        destination=Path('checks')/name/path.relative_to(origin)
        (O/destination).parent.mkdir(parents=True,exist_ok=True)
        data=path.read_bytes()
        (O/destination).write_bytes(data)
        copies.append({'source':str(path),'path':str(destination),'bytes':len(data),'sha256':sha256(data).hexdigest()})
    raw=(origin/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and sha256(raw).hexdigest()==report['sha256']
    records.append({'check':name,'exit_code':report['exit_code'],'raw_bytes':len(raw),
        'source_sha256':report.get('source_sha256'),'copies':copies,
        'claim':'Root ran the check. Owner copied exact actual receipts; no check was run by owner.'})
for name in ['modules.json','strict-checks.json','source-stats.json']:
    data=(A/name).read_bytes()
    (O/'root-metadata').mkdir(exist_ok=True)
    (O/'root-metadata'/name).write_bytes(data)
(O/'check-bindings.json').write_text(json.dumps({'captured_at':datetime.now().astimezone().isoformat(),'checks':records},indent=2)+'\n')

old_source=R/'lean/MicroCFTA/SourcePruningEnumerationInitialRenderCarriers.lean'
new_source=R/'lean/MicroCFTA/SourcePruningEnumerationInitialPartialOutput.lean'
old_bytes=old_source.read_bytes(); new_bytes=new_source.read_bytes()
old_start=old_bytes.index(b'theorem run_initial_finite_render_sound_carriers')
old_end=old_bytes.index(b' := by',old_start)
new_start=new_bytes.index(b'theorem run_initial_finite_render_sound_partial')
new_end=new_bytes.index(b' := by',new_start)
old=old_bytes[old_start:old_end]; new=new_bytes[new_start:new_end]
marker='\n      ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,\n    ∃ (finalInventory : Inventory)'.encode()
cut=new.index(marker)
restored=new[:cut]
closing=') ∧'.encode()
assert restored.endswith(closing)
restored=restored[:-len(closing)]
restored=restored.replace(b'theorem run_initial_finite_render_sound_partial',b'theorem run_initial_finite_render_sound_carriers',1)
opening='    ∃ bound outcome,\n      ('.encode()
assert opening in restored
restored=restored.replace(opening,opening[:-1],1)
assert restored==old
contracts=O/'contracts'; contracts.mkdir(exist_ok=True)
for name,data in [('initial-carriers-original.declaration.txt',old),
                  ('initial-partial-new.declaration.txt',new),
                  ('initial-partial-recovered-old.declaration.txt',restored),
                  ('initial-partial-appended-observer.txt',new[cut:])]:
    (contracts/name).write_bytes(data)
comparison={'status':'PASS','old_source':str(old_source),'new_source':str(new_source),
    'old_source_sha256':sha256(old_bytes).hexdigest(),'new_source_sha256':sha256(new_bytes).hexdigest(),
    'old_declaration_bytes':len(old),'old_declaration_sha256':sha256(old).hexdigest(),
    'recovered_declaration_bytes':len(restored),'recovered_declaration_sha256':sha256(restored).hexdigest(),
    'literal_equal':True,'operations':['Remove only the final partial-output observer and its conjunction.',
        'Remove the one added outer grouping parenthesis around the retained old return.',
        'Restore the theorem name run_initial_finite_render_sound_carriers.'],
    'new_producer_call_count':new_bytes[new_end:].count(b'run_initial_finite_render_sound_carriers'),
    'review':'Entire original declaration retained, including all original admissions, bounds, results, histories and concrete-render observers. No accepting output existence follows from a forall over emitted outputs.'}
assert comparison['new_producer_call_count']==1
(O/'initial-whole-contract-comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')

p=O/'drafts/v1/SourcePruningEnumerationSelectedValue.lean'
passed=json.loads((A/'selected-value-strict-1/report.json').read_text())
installed=R/'lean/MicroCFTA/SourcePruningEnumerationSelectedValue.lean'
assert p.read_bytes()==installed.read_bytes()
assert sha256(p.read_bytes()).hexdigest()==passed['source_sha256']
(O/'selected-value-checked-status.json').write_text(json.dumps({'status':'ROOT_STRICT_FIRST_PASS',
    'draft_initial_status':'UNTESTED (preserved verbatim in original immutable metadata)',
    'draft':str(p),'installed':str(installed),'same_bytes':True,'source_sha256':passed['source_sha256'],
    'exit_code':passed['exit_code'],'raw_bytes':passed['bytes'],'cgroup_limits':passed['cgroup_limits'],
    'proof_runtime_changes_since_draft':'None.','scope':'Actual native heap and least language. No full allocated Caller/Post/Memos/driver integration.'},indent=2)+'\n')
(O/'capture-attempts.json').write_text(json.dumps({'attempts':[
    {'script':'capture_sources.py','status':'FAILED','reason':'Original history public declaration has a direct proof term after := newline; initial extractor expected := by. No proof or repository mutation.'},
    {'script':'capture_sources_v2.py','status':'PASS','change':'Recognize both literal declaration delimiters.'},
    {'script':'capture_sources_v3.py','status':'PASS','change':'Add exact one-value proof dependencies and six current sources.'},
    {'operation':'initial in-memory old-header comparison','status':'FAILED','reason':'Python bytes literal contained Unicode after command serialization; no artifact or source mutation.'},
    {'operation':'initial in-memory old-header comparison, Unicode string encoding','status':'PASS','result':'Whole original 6435-byte declaration literally recovered.'},
    {'script':'capture_checks_and_contract.py','status':'PASS','result':'All actual raw hashes verified; installed selected-value bytes match strict source; whole old startup declaration exact.'}]},indent=2)+'\n')
print(json.dumps({'strict_attempts':len(records),'strict_passes':sum(r['exit_code']==0 for r in records),'strict_failed_attempts':sum(r['exit_code']!=0 for r in records),'old_initial_declaration_bytes':len(old),'old_initial_declaration_sha256':sha256(old).hexdigest()}))
