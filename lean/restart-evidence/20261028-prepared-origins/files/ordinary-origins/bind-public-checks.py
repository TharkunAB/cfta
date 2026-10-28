from pathlib import Path
import json,hashlib,shutil
base=Path('/tmp/mcfta-prepared-origins-20261028'); out=base/'ordinary-origins'
def sha(b): return hashlib.sha256(b).hexdigest()
for name in ['source-validation.json','public-validation.json','audit-summary.json','public-read-scopes.json','source-head.txt','modules.json']:
 src=base/name
 if src.exists():
  d=out/'final-evidence'/name; d.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(src,d)
validation=json.loads((base/'source-validation.json').read_text())
for entry in validation['commands']:
 name=entry['folder']; src=base/name; dest=out/'checks'/name
 for p in sorted(src.rglob('*')):
  if p.is_file():
   d=dest/p.relative_to(src); d.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,d)
 report=json.loads((dest/'report.json').read_text()); raw=(dest/'raw.log').read_bytes()
 assert report['exit_code']==entry['exit_code'] and report['bytes']==len(raw)==entry['bytes'] and report['sha256']==sha(raw)==entry['sha256']
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
public=(out/'checks/public-readback-final/raw.log').read_bytes(); prior=(out/'checks/prior-public-readback/raw.log').read_bytes()
pv=json.loads((out/'final-evidence/public-validation.json').read_text())
assert len(public)==pv['bytes'] and sha(public)==pv['sha256'] and public.startswith(prior) and len(prior)==pv['prior_bytes']
appendix=public[len(prior):]
assert sha(appendix)==pv['new_sha256'] and len(appendix)==pv['new_bytes']
(out/'final-evidence/new-public-blocks.txt').write_bytes(appendix)
scopes=json.loads((out/'final-evidence/public-read-scopes.json').read_text()); reviewed=[]
for r in scopes:
 if r['owner']!='ordinary-origins':continue
 b=appendix[r['offset']:r['offset']+r['bytes']]
 path=out/'public-blocks'/(r['declaration']+'.txt'); assert path.read_bytes()==b and sha(b)==r['sha256']
 first=appendix[:r['offset']].count(b'\n')+1; last=first+b.count(b'\n')-1
 reviewed.append({**r,'path':str(path.relative_to(out)),'source':'final-evidence/new-public-blocks.txt','first_line':first,'last_line':last,'scope':'WHOLE printed theorem signature and WHOLE axiom list read; exact literal byte interval'} )
(out/'public-reviewed-index.json').write_text(json.dumps({'reviewed':reviewed,'full_prior_prefix_verified':True,'readback_sha256':sha(public),'prior_sha256':sha(prior)},indent=2)+'\n')
print(json.dumps({'commands_including_inherited_prior':len(validation['commands']),'current_commands':len(validation['commands'])-1,'current_failures':validation['failures'],'reviewed_public_blocks':len(reviewed),'reviewed_public_bytes':sum(r['bytes'] for r in reviewed),'final_public_bytes':len(public),'prefix_bytes':len(prior)},indent=2))
