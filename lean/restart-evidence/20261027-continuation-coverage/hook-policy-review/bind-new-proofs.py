from pathlib import Path
import json,hashlib,difflib
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-continuation-coverage-20261027');out=area/'hook-policy-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
checks=[]
for check,module,exitcode in [('strict-invocation-1','SourcePruningEnumerationContinuationInvocation',1),('strict-invocation-2','SourcePruningEnumerationContinuationInvocation',1),('strict-invocation-3','SourcePruningEnumerationContinuationInvocation',0),('strict-head-1','SourcePruningEnumerationFiniteHeadCoverage',1),('strict-head-2','SourcePruningEnumerationFiniteHeadCoverage',0)]:
 report=(area/check/'report.json').read_bytes();raw=(area/check/'raw.log').read_bytes();source=(area/check/'MicroCFTA'/f'{module}.lean').read_bytes();r=json.loads(report)
 assert r['exit_code']==exitcode and len(raw)==r['bytes'] and sha(raw)==r['sha256'] and sha(source)==r['source_sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for name,b in [('report.json',report),('raw.log',raw),(f'MicroCFTA/{module}.lean',source)]:put('evidence/'+check+'/'+name,b)
 if exitcode==0:assert source==(repo/'lean/MicroCFTA'/f'{module}.lean').read_bytes()
 checks.append({'check':check,'expected_exit':exitcode,'source_sha256':sha(source),'raw_bytes':len(raw),'raw_sha256':sha(raw),'installed_identical':exitcode==0})
for rel in ['invocation-keyword-repair.json','invocation-keyword-repair.patch','head-namespace-repair.json','head-namespace-repair.patch']:
 put('evidence/'+rel,(area/rel).read_bytes())
index=json.loads((out/'source-index.json').read_text())
for name,spans,scope in [('SourcePruningEnumerationContinuationInvocation',[(25,97)],'Whole final V3 generic helper read; actual prefix observations derive Invocation without next-hook completion. V1/V2 compiler failures retained.'),('SourcePruningEnumerationFiniteHeadCoverage',[(41,122),(123,191)],'Whole installed head V2 read; exact old contract retained, literal actual head/cache bounds, genuine callback resources and appended original model observer.')]:
 src=repo/'lean/MicroCFTA'/f'{name}.lean';b=src.read_bytes();whole='sources/'+src.name;put(whole,b);row={'source':str(src),'whole':{'path':whole,'bytes':len(b),'sha256':sha(b)},'review_scope':scope,'cuts':[]}
 for a,z in spans:
  assert z<=len(b.splitlines());c=b''.join(b.splitlines(keepends=True)[a-1:z]);dest=f'cuts/{src.name}.{a}-{z}.txt';put(dest,c);row['cuts'].append({'path':dest,'bytes':len(c),'sha256':sha(c),'first_line':a,'last_line':z})
 index['sources']=[r for r in index['sources'] if r['source']!=str(src)]+[row]
put('source-index.json',json.dumps(index,indent=2)+'\n')
sibling=area/'sibling-design/drafts/v2/SourcePruningEnumerationFiniteSiblingCoverage.lean';b=sibling.read_bytes();assert sha(b)=='5717fcfb0d1b3f81485ec6a240607cad2387b2764c6cf172180158379378895d';put('reviewed-drafts/sibling-v2.lean',b)
helper2=(area/'strict-invocation-2/MicroCFTA/SourcePruningEnumerationContinuationInvocation.lean').read_text();helper3=(area/'strict-invocation-3/MicroCFTA/SourcePruningEnumerationContinuationInvocation.lean').read_text();assert helper2.split(' := by\n',1)[0]==helper3.split(' := by\n',1)[0]
put('reviewed-drafts/invocation-v2-v3.diff',''.join(difflib.unified_diff(helper2.splitlines(True),helper3.splitlines(True),fromfile='invocation-v2',tofile='invocation-v3')))
contracts=[]
for name,oldfile,theorem,newsource,marker in [('FiniteHeadCoverage','SourcePruningEnumerationFiniteHeadResources','head_finite_complete_resources',(repo/'lean/MicroCFTA/SourcePruningEnumerationFiniteHeadCoverage.lean').read_text(),' ∧\n      ∀ (ambient'),('FiniteSiblingCoverage','SourcePruningEnumerationFiniteSiblingResources','alternatives_finite_complete_resources',b.decode(),' ∧\n      ∀ extra,\n        let work')]:
 old=(repo/'lean/MicroCFTA'/f'{oldfile}.lean').read_text();old=old[old.index('theorem '+theorem+'\n'):].split(' := by\n',1)[0]
 newtheorem=theorem+'_accepting';new=newsource[newsource.index('theorem '+newtheorem+'\n'):].split(' := by\n',1)[0];recovered=new.rsplit(marker,1)[0].replace('theorem '+newtheorem,'theorem '+theorem,1)
 assert old==recovered,name
 put('contracts/'+name+'.original.txt',old);put('contracts/'+name+'.recovered.txt',recovered)
 contracts.append({'module':name,'old_proposition_bytes':len(old.encode()),'old_proposition_sha256':sha(old.encode()),'literal_recovery':True,'mapping':'Delete only appended semantic observer and restore original theorem name.'})
put('contracts/independent-comparison.json',json.dumps({'status':'PASS','contracts':contracts},indent=2)+'\n')
put('evidence/independent-check-binding-open.json',json.dumps({'status':'PASS for listed actual checks; overall review OPEN','checks':checks,'generic_v2_v3_statement_exact':True,'sibling_v2_reviewed_sha256':sha(b),'sibling_v2_check_status':'No compiler result asserted in this record.','reviewer_compiler_runs':0},indent=2)+'\n')
put('drafts/v1/actual-status-after-root-check.json',json.dumps({'original_v1_sha256':'f8082c4749f951ffdb1be396c60caba6a2f0f2f45c3e0b887f972ddc3df32f47','actual_status':'FAILED strict-invocation-1: reserved prefix binder; immutable original preserved.','root_v2_status':'FAILED strict-invocation-2: seven stopped=complete contradictions remained.','root_v3_status':'PASS strict-invocation-3; seven explicit cases completed added. Header unchanged from V2. Installed source 12477724aab5b14b76ddb1bd540ac6b5ef3bbaabfde71be4554ee7beb9593c6e.','reviewer_compiler_runs':0},indent=2)+'\n')
print(json.dumps({'status':'PASS','checks':len(checks),'source_records':len(index['sources']),'cuts':sum(len(r['cuts']) for r in index['sources']),'contracts':contracts}))
