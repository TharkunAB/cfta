from pathlib import Path
import json,hashlib
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-selected-coverage-20261027');out=area/'admission'
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
index=json.loads((out/'source-index.json').read_text())
for name,spans,scope in [('SourcePruningEnumerationSelectedEdgeAdmission',[(1,99)],'whole final installed admission source reviewed; exact original V2 draft and strict source'),('SourcePruningEnumerationSelectedEdgeAccepting',[(1,161)],'whole actual accepted wrapper contract and proof reviewed'),('SourcePruningEnumerationSelectedEdgeCoverage',[(37,114)],'primary full public proposition inspected; remaining proof is retained provenance, reviewed by owner and Root'),('SourcePruningEnumerationSelectedEdgeResources',[(47,96)],'original full proposition inspected for byte-exact recovery; remaining proof provenance only')]:
 src=repo/'lean/MicroCFTA'/f'{name}.lean';b=src.read_bytes();lines=b.splitlines(keepends=True);row={'source_path':str(src),'copy':f'sources/{name}.lean','bytes':len(b),'sha256':sha(b),'review_scope':scope,'cuts':[]};put(row['copy'],b)
 for a,z in spans:
  assert z<=len(lines)
  cut=b''.join(lines[a-1:z]);p=f'cuts/{name}.{a}-{z}.txt';put(p,cut);row['cuts'].append({'path':p,'start_line':a,'end_line':z,'bytes':len(cut),'sha256':sha(cut)})
 assert not any(r['source_path']==str(src) for r in index['sources'])
 index['sources'].append(row)
(out/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
def stmt(name,theorem):
 text=(repo/'lean/MicroCFTA'/f'{name}.lean').read_text();return text[text.index('theorem '+theorem+'\n'):].split(' := by\n',1)[0]
primary=stmt('SourcePruningEnumerationSelectedEdgeCoverage','complete_with_fragments_resources_accepting')
old=stmt('SourcePruningEnumerationSelectedEdgeResources','complete_with_fragments_resources')
recovered=primary.rsplit(' ∧\n      ∀ (ambient',1)[0].replace('theorem complete_with_fragments_resources_accepting','theorem complete_with_fragments_resources',1)
assert recovered==old
put('contracts/original-full-proposition.txt',old);put('contracts/primary-recovered-old-proposition.txt',recovered)
accepted=stmt('SourcePruningEnumerationSelectedEdgeAccepting','accepted_complete')
primary_result=primary[primary.index('    ∃ (r n p h k : Nat)'):]
accepted_group=accepted[accepted.index('    ∃ (r n p h k : Nat)'):].split(') ∧\n      ∃ (extended',1)[0]
accepted_group=accepted_group.replace('      ((∀ er en P H ek,','      (∀ er en P H ek,',1)
assert accepted_group==primary_result
put('contracts/full-primary-result.txt',primary_result);put('contracts/accepted-recovered-primary-result.txt',accepted_group)
put('contracts/accepted-public-statement.txt',accepted)
checks=[]
for d in ['strict-selected-admission-1','strict-selected-accepting-1','build-selected-admission-1','build-selected-coverage-1']:
 src=area/d;report=json.loads((src/'report.json').read_text());raw=(src/'raw.log').read_bytes();assert report['exit_code']==0 and len(raw)==report['bytes'] and sha(raw)==report['sha256']
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for p in src.rglob('*'):
  if p.is_file() and p.name not in ['pins.json','FROZEN.json']:put(str(Path('evidence')/d/p.relative_to(src)),p.read_bytes())
 checks.append({'path':d,'exit_code':0,'raw_bytes':len(raw),'raw_sha256':sha(raw),'cgroup_limits':report['cgroup_limits']})
b=(repo/'lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeAccepting.lean').read_bytes()
assert b==(area/'accepted/drafts/v1/SourcePruningEnumerationSelectedEdgeAccepting.lean').read_bytes()==(area/'strict-selected-accepting-1/MicroCFTA/SourcePruningEnumerationSelectedEdgeAccepting.lean').read_bytes()
put('contracts/independent-contract-validation.json',json.dumps({'status':'PASS','old_full_proposition_bytes':len(old.encode()),'old_full_proposition_sha256':sha(old.encode()),'primary_exact_old_proposition_recovered':True,'accepted_retains_entire_primary_existential_result':True,'primary_result_bytes':len(primary_result.encode()),'primary_result_sha256':sha(primary_result.encode()),'accepted_draft_strict_installed_equal':True,'accepted_sha256':sha(b),'checks':checks,'bundle_status':'OPEN; final public/docs pending'},indent=2)+'\n')
print(json.dumps({'status':'PASS','old_proposition_bytes':len(old.encode()),'entire_primary_result_bytes':len(primary_result.encode()),'source_records':len(index['sources'])}))
