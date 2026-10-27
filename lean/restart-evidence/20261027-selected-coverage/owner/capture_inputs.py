from pathlib import Path
import json,hashlib,datetime
root=Path('/home/tritlo/Code/mcfta')
a=Path('/tmp/mcfta-selected-coverage-20261027/owner')
specs=[
('lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeResources.lean',[(43,201)]),
('lean/MicroCFTA/SourcePruningEnumerationTraversalCoverage.lean',[(30,109)]),
('lean/MicroCFTA/SourcePruningEnumerationEdgeInputs.lean',[(14,99)]),
('lean/MicroCFTA/SourcePruningEnumerationEdgeProjectionLanguage.lean',[(18,74)]),
('lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeFinishLanguage.lean',[(17,30)]),
('lean/MicroCFTA/SourcePruningEnumerationAnnotationHeap.lean',[(20,36)]),
('lean/MicroCFTA/EnumerationSuspendedForward.lean',[(14,47)]),
('lean/MicroCFTA/EnumerationCorrectness.lean',[(756,788)]),
('lean/MicroCFTA/EnumerationConstruction.lean',[(44,49),(141,195)]),
('lean/MicroCFTA/EnumerationSemantics.lean',[(434,452)]),
('lean/MicroCFTA/SourcePruningEnumerationEdgeChildLanguage.lean',[(27,36)]),
('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Data/List/Basic.lean',[(2147,2151)]),
('drafts/v2/SourcePruningEnumerationSelectedEdgeCoverage.lean',[(1,115),(134,244),(281,341)])]
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
records=[]
for p,cuts in specs:
 source=Path(p) if p.startswith('/') else (a/p if p.startswith('drafts/') else root/p)
 b=source.read_bytes();lines=b.splitlines(keepends=True)
 snap=Path('inputs/whole')/source.name
 if snap.exists():raise RuntimeError(str(snap))
 (a/snap).parent.mkdir(parents=True,exist_ok=True);(a/snap).write_bytes(b)
 record={'source':str(source),'snapshot':str(snap),**ident(b),'cuts':[]}
 for first,last in cuts:
  last=min(last,len(lines));cut=b''.join(lines[first-1:last]);cp=Path('inputs/cuts')/(source.stem+f'.L{first}-L{last}.lean.txt')
  (a/cp).parent.mkdir(parents=True,exist_ok=True);(a/cp).write_bytes(cut)
  record['cuts'].append({'snapshot':str(cp),'first_line':first,'last_line':last,**ident(cut),'source_sha256':record['sha256']})
 records.append(record)
(a/'source-index.json').write_text(json.dumps({'hash_convention':'SHA256 of exact bytes; cuts use one-based inclusive line bounds and retain each original LF. Whole copies are labeled snapshot.','captured_at':datetime.datetime.now().astimezone().isoformat(),'sources':records},indent=2)+'\n')
print(len(records),sum(len(r['cuts']) for r in records))
