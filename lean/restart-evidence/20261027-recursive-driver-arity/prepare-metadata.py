from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-driver-arity-20261027');prior=Path('/tmp/mcfta-recursive-worker-arity-20261027')
shorts=['FiniteArityEffects', 'FiniteCallbackResourcesArity', 'FiniteReceiptResourcesArity', 'FiniteHeadResourcesArity', 'FiniteSiblingResourcesArity', 'FiniteSiblingFinishResourcesArity', 'CompletedHeadArity', 'FiniteOrdinaryResourcesArity', 'FiniteOrdinaryForecastResourcesArity', 'FiniteParkedResourcesArity', 'FiniteExpansionResourcesArity', 'FiniteRunStepArity', 'FiniteResourcesArity', 'HistoryPost', 'HistoryOutputArity', 'FiniteHistoryResourcesArity', 'FiniteHistoryRenderingArity']
modules=['SourcePruningEnumeration'+s for s in shorts]
(area/'modules.json').write_text(json.dumps(modules,indent=2)+'\n')
checks={};theorems=[];definitions=[];records=[]
for module in modules:
 source=root/'lean/MicroCFTA'/(module+'.lean');data=source.read_bytes();sha=hashlib.sha256(data).hexdigest()
 matches=[]
 for p in area.glob('strict-*/report.json'):
  r=json.loads(p.read_text())
  if r.get('exit_code')==0 and r.get('bytes')==0 and r.get('source_sha256')==sha: matches.append(p.parent.name)
 assert matches,module
 checks[module]=sorted(matches)[-1]
 ns=None
 for line in data.decode().splitlines():
  m=re.match(r'^namespace MicroCFTA\.(\S+)',line)
  if m: ns=m[1]
  m=re.match(r'^(theorem|def|structure|inductive)\s+(\S+)',line)
  if m:
   assert ns,line
   name=ns+'.'+m[2];(theorems if m[1]=='theorem' else definitions).append(name)
 records.append({'module':module,'bytes':len(data),'lines':len(data.splitlines()),'sha256':sha,'strict':checks[module]})
base=(area/'published-base.txt').read_text().strip()
old_audit=subprocess.check_output(['git','show',base+':lean/MicroCFTA/Audit.lean'],cwd=root)
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==old_audit
(area/'original-Audit.lean').write_bytes(old_audit)
(root/'lean/MicroCFTA/Audit.lean').write_bytes(b''.join(('import MicroCFTA.'+m+'\n').encode() for m in modules)+old_audit)
checks['Audit']='strict-audit-final-1';(area/'strict-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
previous=json.loads((prior/'public-declarations.json').read_text())
(area/'prior-public-declarations.json').write_text(json.dumps(previous,indent=2)+'\n')
p=area/'prior-public-readback';p.mkdir();(p/'raw.log').write_bytes((prior/'public-readback-final-1/raw.log').read_bytes());(p/'report.json').write_bytes((prior/'public-readback-final-1/report.json').read_bytes());(p/'public.lean').write_bytes((prior/'public-readback-final-1/public.lean').read_bytes())
assert len(set(theorems+previous))==len(theorems+previous)
(area/'public-declarations.json').write_text(json.dumps(theorems+previous,indent=2)+'\n');(area/'new-public-declarations.json').write_text(json.dumps(theorems,indent=2)+'\n');(area/'public-definitions.json').write_text(json.dumps(definitions,indent=2)+'\n')
prior_sources=json.loads((prior/'prior-strong-sources.json').read_text())
for module in json.loads((prior/'modules.json').read_text())+['SourceCurrentAllocatedPartialWorkerActual','SourceCurrentAllocatedPartialActual','SourcePruningEnumerationFiniteContract','SourcePruningEnumerationOutcomeResources','SourcePruningEnumerationFiniteHistoryContract','SourcePruningEnumerationNativeBranchResources','SourcePruningEnumerationNativeBranchBoundedResources','SourcePruningEnumerationFiniteResources','SourcePruningEnumerationFiniteHistoryResources']:
 path='lean/MicroCFTA/'+module+'.lean'
 if any(r['path']==path for r in prior_sources):continue
 data=(root/path).read_bytes();assert data==subprocess.check_output(['git','show',base+':'+path],cwd=root)
 prior_sources.append({'module':module,'path':path,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
(area/'prior-strong-sources.json').write_text(json.dumps(prior_sources,indent=2)+'\n')
report={'modules':len(modules),'lines':sum(r['lines'] for r in records),'bytes':sum(r['bytes'] for r in records),'new_public_theorems':len(theorems),'prior_public_theorems':len(previous),'total_public_theorems':len(theorems)+len(previous),'new_public_definitions':definitions,'unchanged_prior_sources':len(prior_sources),'sources':records}
(area/'source-statistics.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='sources'}))
