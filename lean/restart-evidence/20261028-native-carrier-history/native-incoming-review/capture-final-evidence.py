from pathlib import Path
import json,hashlib
R=Path('/home/tritlo/Code/mcfta');B=Path('/tmp/mcfta-native-carriers-20261028');O=B/'native-incoming-review'
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,obj):return put(p,(json.dumps(obj,indent=2)+'\n').encode())
idx=json.loads((O/'source-index.json').read_text());records={x['source']:x for x in idx['sources']}
def stage_record(p,scope,copy_to=None):
 b=p.read_bytes();dst=copy_to or O/'integration-evidence'/p.relative_to(B)
 rec=records.get(str(p),{'source':str(p),'cuts':[]});rec['whole']=put(dst,b);rec['reviewed_scope']=scope;records[str(p)]=rec
stats=json.loads((B/'source-stats.json').read_text())
for z in stats:
 p=R/'lean/MicroCFTA'/(z['module']+'.lean');b=p.read_bytes()
 assert sha(b)==z['sha256'] and len(b)==z['bytes'] and len(b.splitlines())==z['lines']
validation=json.loads((B/'source-validation.json').read_text())
for z in validation['strict_checks']:
 p=R/'lean/MicroCFTA'/(z['module']+'.lean')
 assert sha(p.read_bytes())==z['sha256'] and len(p.read_bytes())==z['bytes']
 report=json.loads((B/z['check']/'report.json').read_text());assert report['exit_code']==0 and report['source_sha256']==z['sha256']
for name in ['source-head.txt','source-commits.json','source-stats.json','source-validation.json','preservation-validation.json','modules.json','strict-checks.json','actual-commands.json','audit-import-insertion.json','root-contract-comparisons.json','traversal-contract-comparison.json','selected-captured-contract-comparisons.json','public-validation.json','public-prefix-comparison.json','public-declarations.json','public-definitions.json','new-public-declarations.json','prior-public-declarations.json','prior-public-definitions.json']:
 stage_record(B/name,'Final source, contract, compiler or installed-public validation record read; cross-checks are recorded in final-evidence-validation.json. This is evidence data, not an independent build.')
checks=[]
commands=json.loads((B/'actual-commands.json').read_text())
for z in commands:
 name=z['name'];d=B/name;r=json.loads((d/'report.json').read_text());assert r==z['report']
 raw=(d/'raw.log').read_bytes();assert len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if 'source_sha256' in r:
  source=Path(r['command'][-1]);assert sha(source.read_bytes())==r['source_sha256']
 for p in sorted(d.rglob('*')):
  if p.is_file() and p.suffix in {'.lean','.json','.log','.txt'}:put(O/'checks'/name/p.relative_to(d),p.read_bytes())
 checks.append({'name':name,'exit_code':r['exit_code'],'bytes':r['bytes'],'sha256':r['sha256'],'source_sha256':r.get('source_sha256')})
public=(B/'public-readback-1/raw.log').read_bytes();prior=(B/'prior-public-readback/raw.log').read_bytes();new=(B/'new-public-blocks.txt').read_bytes();pv=json.loads((B/'public-validation.json').read_text())
assert public==prior+new and len(public)==pv['bytes'] and sha(public)==pv['sha256'] and len(prior)==pv['prior_bytes'] and sha(new)==pv['new_sha256']
for p,scope in [(B/'new-public-blocks.txt','ALL 41 new full theorem signatures and axiom blocks read, lines 1-1843; no new definitions. Middle output truncation in an earlier combined read was replaced by smaller complete reads.'),(B/'public-readback-1/raw.log','All NEW full blocks read. Entire old prefix verified byte-identical; old 268 signatures and 9 definition bodies are preserved but not reread wholesale in this review.'),(B/'public-readback-1/public.lean','Exact installed readback command source and complete public catalogue preserved.'),(B/'public-readback-1/report.json','Actual measured installed readback receipt read and output bytes/hash checked.'),(B/'prior-public-readback/raw.log','Prior exact installed public prefix preserved and compared literally; not a new execution.'),(B/'prior-public-readback/report.json','Inherited prior installed readback receipt; excluded from current 45-command denominator.')]:
 stage_record(p,scope)
# Add the actual Audit identity without asserting a full historical Audit proof review.
p=R/'lean/MicroCFTA/Audit.lean';b=p.read_bytes();dst=O/'sources/lean/MicroCFTA/Audit.lean'
records[str(p)]={'source':str(p),'whole':put(dst,b),'cuts':[],'reviewed_scope':'Current 20 added imports, actual aggregate and strict Audit readbacks checked. Historical Audit body not reread wholesale.'}
audit=json.loads((B/'audit-import-insertion.json').read_text());old_records=json.loads((B/'prior-lean-sources.json').read_text());
# The independent source-preservation report supplies the broad historical denominator. This review pins it and tests the actual current sources used here.
rootcmp=json.loads((B/'root-contract-comparisons.json').read_text())
old=(O/'integration-review/entire-original-initial-proper-declaration.txt').read_bytes()
assert len(old)==4802
trimmed=old.rstrip()
assert len(trimmed)==4801 and sha(trimmed)==rootcmp[0]['sha256']
dump(O/'integration-review/initial-contract-scope-reconciliation.json',{'status':'pass','owner_untrimmed_bytes':len(old),'owner_untrimmed_sha256':sha(old),'root_trimmed_bytes':len(trimmed),'root_trimmed_sha256':sha(trimmed),'difference':'Only the one final blank byte before := by. Both include the entire original theorem declaration and retain the same original producer admission/result.'})
dump(O/'source-index.json',{'sources':list(records.values())})
dump(O/'integration-evidence/final-evidence-validation.json',{'status':'pass','source_head':(B/'source-head.txt').read_text().strip(),'modules':len(stats),'lines':sum(z['lines'] for z in stats),'bytes':sum(z['bytes'] for z in stats),'new_public_theorems':sum(z['public_theorems'] for z in stats),'new_runtime_definitions':0,'current_commands':len(checks),'current_failed_commands':sum(z['exit_code']!=0 for z in checks),'all_current_measured_memory_limits':'4 GiB memory.max/high; swap.max 0','strict_final_modules_plus_Audit':len(validation['strict_checks']),'public':pv,'checks':checks,'review_scope':'Owner five full final modules and recorded underlying contracts; final four Root integration files and receipt dependencies in full; all 41 new public signatures/axioms; other new proof bodies only as explicitly stated in source-index. No compiler, build, Git, native or network command was run by this reviewer.'})
print(json.dumps({'sources':len(records),'cuts':sum(len(z['cuts']) for z in records.values()),'commands':len(checks),'failed':sum(z['exit_code']!=0 for z in checks),'modules':len(stats),'public_new':sum(z['public_theorems'] for z in stats)},indent=2))
