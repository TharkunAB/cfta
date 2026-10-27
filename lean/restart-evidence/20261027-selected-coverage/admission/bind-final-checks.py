from pathlib import Path
import hashlib,json,re
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-selected-coverage-20261027');out=area/'admission';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
for name in ['source-head.txt','statistics.json','strict-checks.json','source-validation.json','public-validation.json','public-declarations.json','prior-public-declarations.json','public-definitions.json','prior-strong-sources.json','audit-import-insertion.json','selected-id-reduction-repair.json']:
 put('final-evidence/'+name,(area/name).read_bytes())
checks=[]
for name in ['strict-forward-descent-1','strict-selected-admission-1','strict-selected-coverage-1','strict-selected-coverage-2','strict-selected-accepting-1','strict-audit-coverage-1','audit-coverage-1','public-readback-1','prior-public-readback']:
 directory=area/name;report=json.loads((directory/'report.json').read_text());raw=(directory/'raw.log').read_bytes()
 assert len(raw)==report['bytes'] and sha(raw)==report['sha256'],name
 if name!='prior-public-readback':
  assert report['exit_code']==(1 if name=='strict-selected-coverage-1' else 0),name
  assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},name
 for p in sorted(directory.rglob('*')):
  if p.is_file() and p.name not in ['pins.json','FROZEN.json']:put(str(Path('final-evidence')/name/p.relative_to(directory)),p.read_bytes())
 checks.append({'check':name,'exit_code':report['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw)})
public=(area/'public-readback-1/raw.log').read_bytes();prior=(area/'prior-public-readback/raw.log').read_bytes();new=(area/'new-public-blocks.txt').read_bytes()
assert public==prior+new and len(prior)==592943 and len(public)==630571
assert sha(public)=='77830f9982c262fde1d9c5afb8b82cb8f899d0aa0890ad976a4790b39226c0c1'
put('final-evidence/new-public-blocks.txt',new)
axioms=re.findall(rb'depends on axioms: \[([^\]]*)\]',public)
assert len(axioms)==168
for aa in axioms:
 assert set(x.strip() for x in aa.replace(b'\n',b' ').split(b',') if x.strip())<={b'Classical.choice',b'Quot.sound',b'propext'}
assert '⋯'.encode() not in public
prior_sources=json.loads((area/'prior-strong-sources.json').read_text());assert len(prior_sources)==86
for row in prior_sources:
 b=(repo/row['path']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'],row['path']
validated=json.loads((area/'source-validation.json').read_text())['strict_checks']
for x in validated:
 name=x['module'];b=(repo/'lean/MicroCFTA'/f'{name}.lean').read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];assert b==(area/x['check']/'MicroCFTA'/f'{name}.lean').read_bytes()
 if name!='Audit':
  installed=area/'installed-sources/lean/MicroCFTA'/f'{name}.lean';assert installed.read_bytes()==b
insert=json.loads((area/'audit-import-insertion.json').read_text());audit=(repo/'lean/MicroCFTA/Audit.lean').read_bytes();old=(area/'prior-sources/Audit.lean').read_bytes();off=insert['insertion_offset'];n=insert['inserted_bytes'];assert audit[:off]+audit[off+n:]==old
put('final-evidence/prior-Audit.lean',old)
put('final-checks-validation.json',json.dumps({'status':'PASS','source_head':(area/'source-head.txt').read_text().strip(),'new_modules':4,'new_public_theorems':5,'new_public_definitions':0,'prior_source_pins_unchanged':86,'entire_prior_public_bytes_literal_prefix':592943,'all_public_bytes':630571,'all_public_sha256':sha(public),'all_axiom_blocks':len(axioms),'standard_axioms_only':True,'strict_snapshots_match_installed':True,'audit_entire_prior_file_inverse':True,'all_checks':checks,'documents':'pending','seal':'OPEN'},indent=2)+'\n')
print(json.dumps({'status':'PASS','all_public_blocks':len(axioms),'new_public_bytes':len(new),'prior_sources':len(prior_sources),'source_head':(area/'source-head.txt').read_text().strip()}))
