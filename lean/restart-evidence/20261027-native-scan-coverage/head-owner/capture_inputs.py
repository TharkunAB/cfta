from pathlib import Path
import json,hashlib,datetime
root=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-native-scan-coverage-20261027/head-owner')
specs=[('SourcePruningEnumerationNativeBranchResources.lean',[(35,167)]),('SourcePruningEnumerationNativeBranchCompletion.lean',[(22,57)]),('SourcePruningEnumerationNativeBranches.lean',[(21,46)]),('SourcePruningEnumerationCapturedEdgeCoverage.lean',[(35,116),(205,278)]),('SourcePruningEnumerationSelectedEdgeAdmission.lean',[(54,101)]),('EnumerationCorrectness.lean',[(125,146)])]
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
records=[]
for name,spans in specs:
 p=root/'lean/MicroCFTA'/name;b=p.read_bytes();lines=b.splitlines(keepends=True)
 wp=Path('inputs/whole')/name;(a/wp).parent.mkdir(parents=True,exist_ok=True);(a/wp).write_bytes(b)
 rec={'source':str(p),'whole':{'path':str(wp),**ident(b)},'cuts':[]}
 for first,last in spans:
  last=min(last,len(lines));cb=b''.join(lines[first-1:last]);cp=Path('inputs/cuts')/(p.stem+f'.L{first}-L{last}.txt');(a/cp).parent.mkdir(parents=True,exist_ok=True);(a/cp).write_bytes(cb)
  rec['cuts'].append({'path':str(cp),**ident(cb),'first_line':first,'last_line':last})
 records.append(rec)
(a/'source-index.json').write_text(json.dumps({'captured_at':datetime.datetime.now().astimezone().isoformat(),'hash_convention':'Exact byte SHA256. Literal cuts use one-based inclusive line ranges and retain original LF. Whole copies are explicitly labeled whole.','sources':records},indent=2)+'\n')
print(json.dumps({'source_wholes':len(records),'literal_cuts':sum(len(r['cuts']) for r in records)},indent=2))
