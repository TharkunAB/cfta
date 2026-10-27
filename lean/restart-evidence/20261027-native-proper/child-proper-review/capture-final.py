from pathlib import Path
import json,hashlib,shutil,re
R=Path('/home/tritlo/Code/mcfta');A=Path('/tmp/mcfta-native-proper-20261027');O=A/'child-proper-review'
h=lambda b:hashlib.sha256(b).hexdigest()
def write(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def cp(src,dst):
 b=src.read_bytes();write(dst,b);return {'path':str(dst),'bytes':len(b),'sha256':h(b)}
idx=json.loads((O/'source-index.json').read_text());ss=idx['sources'];by={s['source']:s for s in ss}
def add_source(src,dest,scope,cut_ranges=()):
 s=by.get(str(src))
 if s is None:
  s={'source':str(src),'whole':cp(src,dest),'cuts':[],'reviewed_scope':scope};ss.append(s);by[str(src)]=s
 else:
  assert src.read_bytes()==Path(s['whole']['path']).read_bytes()
 for first,last,label in cut_ranges:
  b=b''.join(src.read_bytes().splitlines(keepends=True)[first-1:last]);p=O/'final-cuts'/f'{src.name}-{label}-L{first}-L{last}.txt';write(p,b)
  s['cuts'].append({'path':str(p),'bytes':len(b),'sha256':h(b),'first_line':first,'last_line':last})
 return s
# Final exact sources. Additional dependencies have public-contract/identity review only.
valid=json.loads((A/'source-validation.json').read_text())
for v in valid['strict_checks']:
 src=R/'lean/MicroCFTA'/f"{v['module']}.lean";b=src.read_bytes();assert len(b)==v['bytes'] and h(b)==v['sha256']
 scope='Final source identity and full installed public statement reviewed; proof body not independently reviewed in this bundle.'
 if v['module']=='Audit': scope='Final source identity, actual strict Audit receipt and 14-import insertion inverse only; historical Audit body not reviewed.'
 add_source(src,O/'final-sources'/src.name,scope)
# Actual reports and raw outputs, not new executions.
checks=[]
for p in sorted(A.glob('*/report.json')):
 n=p.parent.name;v=json.loads(p.read_text());raw=p.parent/'raw.log';b=raw.read_bytes()
 assert len(b)==v['bytes'] and h(b)==v['sha256']
 assert v['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 cp(p,O/'final-checks'/n/'report.json');cp(raw,O/'final-checks'/n/'raw.log')
 for snap in p.parent.glob('MicroCFTA/*.lean'):
  sb=snap.read_bytes()
  if v.get('source_sha256'):assert h(sb)==v['source_sha256']
  cp(snap,O/'final-checks'/n/'MicroCFTA'/snap.name)
 for snap in p.parent.glob('public.lean'):cp(snap,O/'final-checks'/n/'public.lean')
 checks.append({'name':n,'exit_code':v['exit_code'],'bytes':len(b),'sha256':h(b),'source_sha256':v.get('source_sha256')})
assert len(checks)==27
assert sorted((x['name'],x['bytes']) for x in checks if x['exit_code']!=0)==[('child-proper-strict-1',677),('terminal-proper-strict-1',9823)]
write(O/'final-checks'/'verified-receipts.json',(json.dumps(checks,indent=2)+'\n').encode())
# Exact public prefix and new complete blocks.
old=(A/'prior-public-readback/raw.log').read_bytes();new=(A/'public-readback-1/raw.log').read_bytes();blocks=(A/'new-public-blocks.txt').read_bytes()
assert len(old)==792434 and len(new)==857288 and new==old+blocks and len(blocks)==64854 and len(blocks.splitlines())==939
assert new.count(b'depends on axioms:')==212 and blocks.count(b'depends on axioms:')==30
cp(A/'prior-public-readback/raw.log',O/'public/prior-182-blocks.log');cp(A/'new-public-blocks.txt',O/'public/new-30-blocks.txt')
write(O/'public/exact-prefix-verification.json',(json.dumps({'status':'PASS','old_bytes':len(old),'old_sha256':h(old),'new_full_bytes':len(new),'new_full_sha256':h(new),'new_suffix_bytes':len(blocks),'new_suffix_sha256':h(blocks),'old_blocks':182,'new_blocks':30,'exact_prefix_and_suffix':True},indent=2)+'\n').encode())
# Root old contracts are preserved literally; same original-producer-once source checked.
for prefix in ['initial','captured']:
 oldc=(A/f'root-contracts/{prefix}-old-declaration.txt').read_bytes();rec=(A/f'root-contracts/{prefix}-recovered-declaration.txt').read_bytes();assert oldc==rec
for f in sorted((A/'root-contracts').glob('*.txt')):cp(f,O/'root-contracts'/f.name)
# Final note whole source read. Current docs: literal insert plus original whole bytes.
docs=json.loads((A/'document-validation.json').read_text());doc_checks=[];shared=[]
for v in docs:
 src=R/v['path'];b=src.read_bytes();assert len(b)==v['bytes'] and h(b)==v['sha256']
 if 'offset' not in v:
  add_source(src,O/'documents'/v['path'],'Whole final new note read; claims checked against actual source/public/receipts.')
  continue
 off=v['offset'];size=v['inserted_bytes'];ins=b[off:off+size];old=(A/'prior-documents'/v['path']).read_bytes()
 assert b[:off]+b[off+size:]==old and len(old)==v['old_bytes'] and h(old)==v['old_sha256']
 prior=cp(A/'prior-documents'/v['path'],O/'documents/prior-documents'/v['path'])
 ip=O/'documents/insertions'/v['path'];write(ip,ins)
 first=b[:off].count(b'\n')+1;last=first+ins.count(b'\n')-(1 if ins.endswith(b'\n') else 0)
 assert b''.join(b.splitlines(keepends=True)[first-1:last])==ins
 ss.append({'source':str(src),'source_bytes':len(b),'source_sha256':h(b),'cuts':[{'path':str(ip),'bytes':len(ins),'sha256':h(ins),'first_line':first,'last_line':last}],
 'reconstruction':{'prior':prior,'insert':{'path':str(ip),'bytes':len(ins),'sha256':h(ins)},'offset':off},'reviewed_scope':'Entire new insertion read. Old whole body retained and exact removal inverse checked; historical prose not reread.'})
 baseline=A/'prior-documents'/v['path'];ss.append({'source':str(baseline),'whole':prior,'cuts':[],'reviewed_scope':'Whole original byte identity and exact current-document removal inverse; historical prose not reread.'})
 shared.append(ins[:2070]);doc_checks.append({'path':v['path'],'offset':off,'inserted_bytes':size,'inserted_sha256':h(ins),'old_bytes':len(old),'old_sha256':h(old),'current_bytes':len(b),'current_sha256':h(b),'exact_old_body_inverse':True})
assert len(shared)==9 and all(x==shared[0] for x in shared)
write(O/'documents/independent-inverse-verification.json',(json.dumps({'status':'PASS','identical_common_prefix_bytes':2070,'identical_common_prefix_sha256':h(shared[0]),'documents':doc_checks},indent=2)+'\n').encode())
# Metadata is copied from the current stage, not other agents' evolving reports.
for n in ['actual-commands.json','helper-attempts.json','source-validation.json','public-validation.json','public-prefix-comparison.json','preservation-validation.json','document-validation.json','document-paths.json','root-contract-comparisons.json','audit-import-insertion.json','source-head.txt','source-commits.json','published-base.txt','modules.json','strict-checks.json','new-public-declarations.json','prior-strong-sources.json','prior-lean-sources.json','prior-haskell-sources.json']:
 cp(A/n,O/'final-metadata'/n)
write(O/'source-index.json',(json.dumps(idx,indent=2)+'\n').encode())
print(json.dumps({'sources':len(ss),'cuts':sum(len(s.get('cuts',[])) for s in ss),'actual_reports':len(checks),'docs':len(doc_checks),'public_prefix_exact':True,'new_full_blocks':30},indent=2))
