from pathlib import Path
import json,hashlib,datetime
out=Path('/tmp/mcfta-recursive-composition-20261027/selected-canonical-draft');repo=Path('/home/tritlo/Code/mcfta');sha=lambda b:hashlib.sha256(b).hexdigest()
def write(path,data):
 p=out/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
def js(path,data):write(path,(json.dumps(data,indent=2)+'\n').encode())
inputs=[
('SourcePruningEnumerationPrefixLanguage',[(114,171),(177,192),(195,213)]),
('SourcePruningEnumerationSelectedPrefixCanonical',[(18,24),(57,73)]),
('SourcePruningEnumerationPrefixCompletion',[(31,47)]),
('SourcePruningEnumerationRecursivePrefixLanguage',[(49,83)]),
('SourcePruningEnumerationRecursivePacket',[(21,40)]),
('EnumerationValidity',[(18,60)]),
('SourcePruningEnumerationTerminalCanonical',[(28,36)]),
('SourcePruningEnumerationRecursiveCallbackCanonical',[(35,57)]),
('SourcePruningEnumerationSelectedStepCompletion',[(308,352)]),
('SourcePruningEnumerationSelectedStep',[(43,103)])]
sources=[];cuts=[]
for name,parts in inputs:
 path=repo/'lean/MicroCFTA'/(name+'.lean');raw=path.read_bytes();dest=Path('inputs/lean/MicroCFTA')/(name+'.lean');write(dest,raw)
 sources.append({'path':str(path),'source':str(path),'snapshot':str(dest),'bytes':len(raw),'sha256':sha(raw),'read_scope':'Used contracts and relevant proofs as report.txt; full copy records identity, not full import closure'})
 lines=raw.splitlines(keepends=True)
 for start,end in parts:
  assert 1<=start<=end<=len(lines),(name,start,end,len(lines))
  data=b''.join(lines[start-1:end]);dest=Path('cuts')/(name+f'--{start}-{end}.lean');write(dest,data)
  cuts.append({'path':str(path),'source':str(path),'snapshot':str(dest),'start':start,'end':end,'source_sha256':sha(raw),'bytes':len(data),'sha256':sha(data)})
draft=out/'SourcePruningEnumerationPrefixCanonicalHistory.lean';text=draft.read_text();old=(repo/'lean/MicroCFTA/SourcePruningEnumerationPrefixLanguage.lean').read_text()
checks=[]
for oldname,newname,oldend,newend in [('retained_action','retained_action_success','\nend Runtime','\n\nvariable [DecidableEq Symbol]'),('finish_preserves','finish_cache_fields','\n/-- The valid actual prefix','\n\n/-- Every retained cache')]:
 start=old.index('private theorem '+oldname+'\n');stop=old.index(oldend,start);expected=old[start:stop].strip().replace('private theorem '+oldname+'\n','private theorem '+newname+'\n')
 start=text.index('private theorem '+newname+'\n');stop=text.index(newend,start);actual=text[start:stop].strip();assert expected==actual
 checks.append({'source':'lean/MicroCFTA/SourcePruningEnumerationPrefixLanguage.lean','original':oldname,'draft':newname,'only_change':'private theorem name','normalized_outer_whitespace_bytes':len(actual.encode()),'sha256':sha(actual.encode()),'literal_body_equal':True})
js(Path('helper-provenance.json'),checks)
js(Path('draft-scope.json'),{'module':'SourcePruningEnumerationPrefixCanonicalHistory','status':'UNBUILT SOURCE-ONLY DRAFT','public_theorems':['SourcePruningEnumerationSelectedStep.prefix_canonical','SourcePruningEnumerationRecursive.packet_prefix_complete_semantics_canonical'],'public_theorem_count':2,'private_helpers':2,'runtime_definitions':0,'new_datatypes':0,'new_predicates':0,'new_instances':0,'existing_local_instance_activation':'SourcePruningEnumerationAction.actionMonadList','original_packet_unchanged':True,'old_semantic_producer_calls':1,'new_original_input':'Canonical before.core','future_execution_or_desired_endpoint_premises':False,'retained_outputs':['same bound','entire old PrefixValid family','entire old PrefixMeaning family'],'new_output':'Canonical at each actual retained parked/narrowed cache','lines':len(text.splitlines()),'bytes':draft.stat().st_size,'sha256':sha(draft.read_bytes())})
index={'version':1,'status':'FROZEN SOURCE-ONLY DRAFT; NOT CHECKED','observed_at':datetime.datetime.now().astimezone().isoformat(),'sources':sources,'cuts':cuts,'drafts':[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in [draft,*sorted((out/'revisions').glob('*.lean'))]],'read_scope':'report.txt','unreviewed_imports':'All imported implementations outside the ten pinned sources and their labeled spans; no claim of closure audit'}
js(Path('source-pins.json'),index)
for s in sources:assert (out/s['snapshot']).read_bytes()==Path(s['source']).read_bytes()
for c in cuts:assert (out/c['snapshot']).read_bytes()==b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']])
payloads=[p for p in sorted(out.rglob('*'))if p.is_file()and p not in {out/'pins.json',out/'FROZEN.json'}]
pins={'version':1,'pins':[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in payloads]};js(Path('pins.json'),pins);pinraw=(out/'pins.json').read_bytes()
f={'status':'FROZEN SOURCE/DATA ONLY; NO LEAN VALIDATION CLAIM','pins_count':len(payloads),'pins_bytes':len(pinraw),'pins_sha256':sha(pinraw),'source_count':len(sources),'cut_count':len(cuts),'cut_lines':sum(c['end']-c['start']+1 for c in cuts),'draft_sha256':sha(draft.read_bytes()),'report_sha256':sha((out/'report.txt').read_bytes()),'source_pins_sha256':sha((out/'source-pins.json').read_bytes()),'compiler_executed':False};js(Path('FROZEN.json'),f)
assert {x['path']for x in pins['pins']}|{'pins.json','FROZEN.json'}=={str(p.relative_to(out))for p in out.rglob('*')if p.is_file()}
print(json.dumps(f,indent=2));print('FROZEN SHA256',sha((out/'FROZEN.json').read_bytes()));print('Exact files',len(payloads)+2)
