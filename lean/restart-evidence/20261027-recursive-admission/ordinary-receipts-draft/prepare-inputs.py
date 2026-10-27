from pathlib import Path
import json,hashlib,datetime
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-recursive-admission-20261027/ordinary-receipts-draft');sha=lambda b:hashlib.sha256(b).hexdigest()
sources=[];cuts=[]
def add(name,spans=[],decls=[],scope='used contract read'):
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();text=b.decode();dest='inputs/lean/MicroCFTA/'+name+'.lean';q=out/dest;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 sources.append({'path':str(p),'source':str(p),'snapshot':dest,'bytes':len(b),'sha256':sha(b),'read_scope':scope})
 parts=list(spans)
 for key in decls:
  pos=text.index('theorem '+key);end=text.index(' := by',pos)+len(' := by');parts.append((text[:pos].count('\n')+1,text[:end].count('\n')+1))
 lines=b.splitlines(keepends=True)
 for start,end in parts:
  assert 1<=start<=end<=len(lines),(name,start,end,len(lines))
  raw=b''.join(lines[start-1:end]);dest=f'cuts/{name}--{start}-{end}.lean';q=out/dest;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
  cuts.append({'path':str(p),'source':str(p),'snapshot':dest,'start':start,'end':end,'source_sha256':sha(b),'bytes':len(raw),'sha256':sha(raw)})
add('SourcePruningEnumerationOrdinaryInvocationResources',decls=['ordinary_finite_complete_resources_with_invocations','ordinary_finite_complete_invocation_resources'],scope='whole final new module read; proof-only correction compared exactly')
add('SourcePruningEnumerationFiniteOrdinaryResources',decls=['ordinary_finite_complete_resources'],scope='whole old producer header and proof read')
add('SourcePruningEnumerationOrdinaryInvocation',[(27,36)],scope='actual OrdinaryInvocation definition and output provenance read')
add('SourcePruningEnumerationInvocationReceipts',decls=['alternatives_finite_invocation_receipts'],scope='whole previously checked helper reused at actual entered cache; exact current source')
add('SourcePruningEnumerationHeadAdmission',[(41,66),(71,102)],scope='actual input/returned full memo and Packet receipt contracts read; earlier peer checked wrapper')
add('SourcePruningEnumerationRecursivePacket',[(21,35),(43,48)],scope='whole original Packet/transport/receipt contracts read')
add('SourcePruningEnumerationFiniteResources',decls=['finite_complete'],scope='whole original finite depth induction and original run wrapper read')
add('SourcePruningEnumerationSuspendedMass',[(89,94)],scope='used suspendedBound_values identity read; unrelated mass lemmas not freshly audited')
add('EnumerationDriver',[(397,403),(664,669)],scope='Ready and RenderStable fields read; unrelated graph proof suffixes not freshly audited')
add('EnumerationReferences',[(371,377)],scope='actual incoming_read transport read; unrelated reference proofs not freshly audited')
add('EnumerationSchedule',[(272,279)],scope='IsRoot/LiveRoots definitions read; unrelated scheduler proof suffixes not freshly audited')
add('EnumerationExpandableIndex',[(15,19),(46,49)],scope='actual Cached carrier and frame definition read; unrelated cache proofs not freshly audited')
index={'version':1,'status':'OPEN CLEAR SOURCE REVIEW; SEAL HELD FOR ROOT CONSUMER','observed_at':datetime.datetime.now().astimezone().isoformat(),'sources':sources,'cuts':cuts,'new_compiler_checks_executed':False,'read_scope':'report.txt; exact current sources and focused used definitions, no broad import closure audit'}
(out/'source-pins.json').write_text(json.dumps(index,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':index['status'],'sources':len(sources),'cuts':len(cuts),'cut_lines':sum(c['end']-c['start']+1 for c in cuts)},indent=2))
