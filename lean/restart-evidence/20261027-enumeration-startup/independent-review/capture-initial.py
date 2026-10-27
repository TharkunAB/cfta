from pathlib import Path
import hashlib,json
A=Path('/tmp/mcfta-enumeration-startup-20261027');R=Path('/home/tritlo/Code/mcfta');D=A/'independent-review'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(rel,b):p=D/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
records=[]
def source(path,rel,cuts,scope):
 b=path.read_bytes();write(rel,b);r={'source_path':str(path),'copy':rel,'bytes':len(b),'sha256':sha(b),'review_scope':scope,'cuts':[]}
 for first,last,label in cuts:
  cb=b''.join(b.splitlines(keepends=True)[first-1:last]);dst=f'cuts/{path.stem}-{first}-{last}-{label}.txt';write(dst,cb);r['cuts'].append({'path':dst,'start_line':first,'end_line':last,'bytes':len(cb),'sha256':sha(cb)})
 records.append(r)
source(A/'initial-packet/drafts/v1/SourcePruningEnumerationInitialPacket.lean','drafts/SourcePruningEnumerationInitialPacket.lean',[(29,50,'startup-contract'),(51,88,'actual-derived-packet')],'Whole draft read')
for name,cuts,scope in [
 ('EnumerationState.lean',[(67,78,'six-fields-initial')],'Only listed initial state cut read; whole source is provenance'),
 ('SourcePruningEnumerationNodes.lean',[(15,49,'handle-readback')],'Whole source read'),
 ('SourcePruningEnumerationNativeIndex.lean',[(16,29,'native-candidate')],'Candidate and write admission sections through line 150 read; remaining code is provenance'),
 ('SourcePruningEnumerationRecursivePacket.lean',[(20,36,'six-invariant-fields')],'Whole source read'),
 ('SourcePruningEnumerationFiniteHistoryRenderingArity.lean',[(32,101,'full-existing-render-contract')],'Whole source read'),
 ('SourcePruningEnumerationRendering.lean',[(23,26,'discharged')],'Only Discharged definition read; renderer was reviewed at earlier frozen checkpoint'),
 ('EnumerationCanonicalWaiting.lean',[(100,104,'empty-initial-counts')],'Definitions and initial correctness through line 125 read; remaining code is provenance')]:source(R/'lean/MicroCFTA'/name,'inputs/'+name,cuts,scope)
for rel,cuts in [
 ('cfta/src/Data/CFTA/Enumeration.hs',[(228,272,'physical-state-fields'),(294,312,'literal-startup'),(469,474,'expandable'),(1049,1081,'render-boundary'),(1156,1166,'prune-entry'),(1180,1193,'until-entry')]),
 ('cfta/src/Data/CFTA/Internal/UnionFind.hs',[(46,55,'first-uvar-zero'),(83,93,'singletons')]),
 ('cfta/src/Data/CFTA/Interned/Type.hs',[(608,611,'recursive-boundary')])]:source(R/rel,'haskell/'+rel.split('cfta/src/',1)[1],cuts,'Only the listed literal source cuts read; whole source is provenance')
for p in sorted((A/'strict-initial-packet-1').rglob('*')):
 if p.is_file():
  rel='evidence/strict-initial-packet-1/'+str(p.relative_to(A/'strict-initial-packet-1'));b=p.read_bytes();write(rel,b);records.append({'source_path':str(p),'copy':rel,'bytes':len(b),'sha256':sha(b),'review_scope':'Actual Root strict source/report/raw; no compiler run by reviewer'})
report=json.loads((A/'strict-initial-packet-1/report.json').read_text());b=(A/'strict-initial-packet-1/raw.log').read_bytes();draft=(A/'initial-packet/drafts/v1/SourcePruningEnumerationInitialPacket.lean').read_bytes();snap=(A/'strict-initial-packet-1/MicroCFTA/SourcePruningEnumerationInitialPacket.lean').read_bytes()
assert draft==snap and report['source_sha256']==sha(draft) and report['exit_code']==0 and b==b'' and report['bytes']==0 and report['sha256']==sha(b)
assert report['cgroup_limits']['memory.max']=='4294967296' and report['cgroup_limits']['memory.swap.max']=='0'
write('source-pins-initial.json',(json.dumps({'sources':records},indent=2)+'\n').encode())
print(len(records),'records;',sum(len(r.get('cuts',[])) for r in records),'literal cuts')
