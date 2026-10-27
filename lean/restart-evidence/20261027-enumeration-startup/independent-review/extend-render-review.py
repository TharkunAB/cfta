from pathlib import Path
import json,hashlib,re
A=Path('/tmp/mcfta-enumeration-startup-20261027');R=Path('/home/tritlo/Code/mcfta');D=A/'independent-review'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(rel,b):p=D/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
index=json.loads((D/'source-pins-initial.json').read_text());records=index['sources']
# Clamp the initial proof cut to its actual final line. The source bytes are unchanged.
first=records[0];cut=first['cuts'][1];assert len((D/first['copy']).read_bytes().splitlines())==86
oldpath=D/cut['path'];newpath=cut['path'].replace('-51-88-','-51-86-');oldpath.rename(D/newpath);cut['path']=newpath;cut['end_line']=86
(D/'source-pins-initial.json').write_text(json.dumps(index,indent=2)+'\n')
def copy(p,rel,scope):
 b=p.read_bytes();save(rel,b);rec={'source_path':str(p),'copy':rel,'bytes':len(b),'sha256':sha(b),'review_scope':scope};records.append(rec);return rec
p=A/'startup-render/drafts/v1/SourcePruningEnumerationInitialRendering.lean';rec=copy(p,'drafts/SourcePruningEnumerationInitialRendering.lean','Whole source read');b=p.read_bytes();rec['cuts']=[]
for a,z,label in [(33,94,'full-specialized-contract'),(95,110,'same-producer-composition')]:
 cb=b''.join(b.splitlines(keepends=True)[a-1:z]);rel=f'cuts/SourcePruningEnumerationInitialRendering-{a}-{z}-{label}.txt';save(rel,cb);rec['cuts'].append({'path':rel,'start_line':a,'end_line':z,'bytes':len(cb),'sha256':sha(cb)})
for cn in ['strict-initial-rendering-1','build-initial-packet-1']:
 rp=A/cn/'report.json';rep=json.loads(rp.read_text());raw=(A/cn/'raw.log').read_bytes();assert rep['exit_code']==0 and rep['bytes']==len(raw) and rep['sha256']==sha(raw)
 assert rep['cgroup_limits']['memory.max']=='4294967296' and rep['cgroup_limits']['memory.swap.max']=='0'
 if cn.startswith('strict'):
  assert raw==b'' and rep['source_sha256']==sha(b) and (A/cn/'MicroCFTA'/p.name).read_bytes()==b
 for q in sorted((A/cn).rglob('*')):
  if q.is_file():copy(q,'evidence/'+cn+'/'+str(q.relative_to(A/cn)),'Actual Root source/check/build evidence; reviewer ran no compiler')
# Compare the full old result and actual specialized result independently.
old=(R/'lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryRenderingArity.lean').read_text();new=p.read_text()
def result(t):
 start=t.index('    ∃ bound outcome,');end=t.index(' := by',start);return t[start:end]
oldresult=result(old);newresult=result(new)
removed='        before.core.values[uv]? = some (.unenumerated (some handle) bucket) →\n        lookupNode caller.checked.native.machine.heap handle = some value →\n'
specialized=oldresult.replace('(fuel uv : Nat)','(fuel : Nat)',1)
specialized=specialized.replace('          (after : Core) (term : Language.Term Symbol) (pending : List (Constraint × Language.Term Symbol))\n          (handle : Nat) (bucket : List Suspended) (value : Node),','          (after : Core) (term : Language.Term Symbol) (pending : List (Constraint × Language.Term Symbol)),',1)
assert removed in specialized;specialized=specialized.replace(removed,'',1)
specialized=specialized.replace('marker fuel uv','marker fuel 0',1).replace('∀ sc ∈ bucket,','∀ sc ∈ ([] : List Suspended),',1).replace('term = assignment uv','term = assignment 0',1)
assert specialized==newresult
root=j=json.loads((A/'startup-render/contract-derivation-v1.json').read_text());assert root['prior_full_result']==oldresult and root['specialized_full_result']==newresult
for tag,text in [('old-result',oldresult),('actual-startup-result',newresult),('independently-specialized-result',specialized)]:save('contracts/'+tag+'.lean.txt',text.encode())
copy(A/'startup-render/contract-derivation-v1.json','contracts/root-contract-derivation-v1.json','Root mapping independently checked against actual old/new source strings')
comparison={'status':'PASS','old_result_bytes':len(oldresult.encode()),'old_result_sha256':sha(oldresult.encode()),'new_result_bytes':len(newresult.encode()),'new_result_sha256':sha(newresult.encode()),'specialized_byte_exact':True,'fixed_arguments':{'uv':0,'bucket':[],'handle':'derived by initial_packet','value':'original closed available root'},'removed_observer_antecedents':removed,'derived_original_admissions':['Packet','Canonical','initialMass using 0≤ceiling'],'retained_original_admissions':['native Context/full Memos','numeric Fits','guard carrier','selector membership/length','finite reservation','genuine initial arity Heap'],'scope':'Specialization to literal startup, not a claim that the arbitrary-cache old theorem header is unchanged.'}
save('contract-independent-validation.json',(json.dumps(comparison,indent=2)+'\n').encode());save('source-pins-current.json',(json.dumps({'sources':records},indent=2)+'\n').encode())
print(json.dumps(comparison,indent=2))
