from pathlib import Path
import hashlib,json,datetime
root=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-selector-capture-20261027/captured-owner')
specs=[
('SourcePruningEnumerationCapturedEdgeResources.lean',[(32,215)]),
('SourcePruningEnumerationSelectedEdgeCoverage.lean',[(34,116),(298,341)]),
('SourcePruningEnumerationFinalizeLanguage.lean',[(19,49)]),
('SourcePruningEnumerationFinalize.lean',[(15,69),(112,145)]),
('EnumerationFrame.lean',[(475,501)]),
('EnumerationCorrectness.lean',[(125,146)]),
('InternedGuardedLanguage.lean',[(127,141)]),
('SourcePruningEnumerationCapturedEdge.lean',[(25,38)]),
('SourcePruningEnumerationCapturedEdgeResourceSoundness.lean',[(169,212)]),
('SourcePruningEnumerationCapturedEdgeSoundness.lean',[(137,164)])]
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
records=[]
for name,spans in specs:
 source=root/'lean/MicroCFTA'/name;b=source.read_bytes();lines=b.splitlines(keepends=True)
 whole=Path('inputs/whole')/name;(a/whole).parent.mkdir(parents=True,exist_ok=True);(a/whole).write_bytes(b)
 r={'source':str(source),'whole':{'path':str(whole),**ident(b)},'cuts':[]}
 for first,last in spans:
  last=min(last,len(lines));cut=b''.join(lines[first-1:last]);cp=Path('inputs/cuts')/(source.stem+f'.L{first}-L{last}.lean.txt')
  (a/cp).parent.mkdir(parents=True,exist_ok=True);(a/cp).write_bytes(cut)
  r['cuts'].append({'path':str(cp),**ident(cut),'first_line':first,'last_line':last})
 records.append(r)
(a/'source-index.json').write_text(json.dumps({'hash_convention':'SHA256 of exact file bytes; cuts use one-based inclusive bounds and retain the original trailing LF. Source records are actual repository inputs.','captured_at':datetime.datetime.now().astimezone().isoformat(),'sources':records},indent=2)+'\n')
print(json.dumps({'sources':len(records),'cuts':sum(len(x['cuts']) for x in records)},indent=2))
