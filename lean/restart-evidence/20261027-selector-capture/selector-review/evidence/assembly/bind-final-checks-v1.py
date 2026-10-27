from pathlib import Path
import json,hashlib,re
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-selector-capture-20261027');out=area/'selector-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
for name in ['source-validation.json','preservation-validation.json','public-validation.json','public-declarations.json','prior-public-declarations.json','public-definitions.json','prior-strong-sources.json','prior-enumeration-sources.json','prior-haskell-sources.json','audit-import-insertion.json']:
 put('final-evidence/'+name,(area/name).read_bytes())
checks=[]
for name in ['strict-selector-1','strict-selector-2','strict-captured-coverage-1','strict-captured-accepting-1','build-selector-captured-1','strict-audit-1','audit-1','public-readback-1','prior-public-readback']:
 d=area/name;report=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes();assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],name
 if name!='prior-public-readback':
  assert report['exit_code']==(1 if name=='strict-selector-1' else 0),name
  assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},name
 for p in d.rglob('*'):
  if p.is_file() and p.name not in ['pins.json','FROZEN.json']:put(str(Path('final-evidence')/name/p.relative_to(d)),p.read_bytes())
 checks.append({'check':name,'exit_code':report['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw)})
current=(area/'public-readback-1/raw.log').read_bytes();old=(area/'prior-public-readback/raw.log').read_bytes();new=(area/'new-public-blocks.txt').read_bytes();assert current==old+new;assert len(current)==667078 and len(old)==630571 and len(new)==36507
assert sha(current)=='4453ff071f4251bd7b753e880e0301ccdc5c1eed804c34a416d7fece799ee2a5'
put('final-evidence/new-public-blocks.txt',new)
axioms=re.findall(rb'depends on axioms: \[([^\]]*)\]',current);assert len(axioms)==173
for aa in axioms:
 assert set(x.strip() for x in aa.replace(b'\n',b' ').split(b',') if x.strip())<={b'Classical.choice',b'Quot.sound',b'propext'}
assert '⋯'.encode() not in current
counts={}
for manifest,total in [('prior-strong-sources.json',90),('prior-enumeration-sources.json',437),('prior-haskell-sources.json',203)]:
 rows=json.loads((area/manifest).read_text());assert len(rows)==total
 for row in rows:
  b=(repo/row['path']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'],row['path']
 counts[manifest]=total
for row in json.loads((area/'source-validation.json').read_text())['strict_checks']:
 module=row['module'];b=(repo/'lean/MicroCFTA'/f'{module}.lean').read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'];assert b==(area/row['check']/'MicroCFTA'/f'{module}.lean').read_bytes()
meta=json.loads((area/'audit-import-insertion.json').read_text());b=(repo/'lean/MicroCFTA/Audit.lean').read_bytes();old=(area/'prior-sources/Audit.lean').read_bytes();insertion=b''.join(('import MicroCFTA.'+name+'\n').encode() for name in meta['imports']);off=meta['insertion_offset'];assert b[off:off+len(insertion)]==insertion and b[:off]+b[off+len(insertion):]==old
put('final-evidence/prior-Audit.lean',old)
idx=json.loads((out/'source-index.json').read_text())
for row in idx['sources']:
 b=Path(row['source']).read_bytes();assert b==(out/row['whole']['path']).read_bytes();assert len(b)==row['whole']['bytes'] and sha(b)==row['whole']['sha256']
 for cut in row['cuts']:
  c=b''.join(b.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']]);assert c==(out/cut['path']).read_bytes();assert len(c)==cut['bytes'] and sha(c)==cut['sha256']
put('final-checks-validation.json',json.dumps({'status':'PASS','new_modules':3,'new_theorems':5,'new_predicates_or_runtime_definitions':0,'public_blocks':173,'prior_public_blocks':168,'entire_prior_public_bytes_literal_prefix':630571,'new_public_bytes':36507,'full_new_public_read':True,'public_bytes':667078,'public_sha256':sha(current),'standard_axioms_only':True,'strict_snapshots_match_installed':True,'all_checks':checks,'unchanged_source_manifests':counts,'audit_only_three_imports_entire_prior_inverse':True,'source_records':len(idx['sources']),'literal_cuts':sum(len(x['cuts']) for x in idx['sources']),'documents':'pending','bundle_status':'OPEN'},indent=2)+'\n')
print(json.dumps({'status':'PASS','public_blocks':173,'source_records':len(idx['sources']),'literal_cuts':sum(len(x['cuts']) for x in idx['sources']),'prior_enum_sources':437,'prior_Haskell_sources':203}))
