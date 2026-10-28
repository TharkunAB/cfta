from pathlib import Path
import json,hashlib
own=Path('/tmp/mcfta-prepared-composition-20261028/selector-admission');area=own.parent;repo=Path('/home/tritlo/Code/mcfta')
sha=lambda b:hashlib.sha256(b).hexdigest()
def save(rel,b):
 p=own/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'path':str(rel),'bytes':len(b),'sha256':sha(b)}
def cp(src,rel):return save(rel,Path(src).read_bytes())
def js(rel,data):return save(rel,(json.dumps(data,indent=2)+'\n').encode())
idx=json.loads((own/'source-index.json').read_text())
def source(rel,spans,scope,dst=None):
 p=repo/rel;b=p.read_bytes();lines=b.splitlines(keepends=True);r={'source':str(p),'whole':cp(p,dst or 'sources/'+rel),'cuts':[],'inspected_scope':scope}
 for a,z in spans:
  z=min(z,len(lines));assert 1<=a<=z
  r['cuts'].append(dict(save('cuts/'+p.stem+f'.L{a}-{z}.txt',b''.join(lines[a-1:z])),first_line=a,last_line=z))
 idx['sources'].append(r)
source('lean/MicroCFTA/SourcePruningEnumerationPrefixCheckpointOrigins.lean',[(25,63),(84,140),(141,160)],'whole final installed source and whole printed declarations; exact original retained grouping independently checked')
source('lean/MicroCFTA/SourcePruningEnumerationPreparedPrefixOrigins.lean',[(35,91),(92,169),(170,213)],'whole final installed source and whole printed declaration; failed v1 grouping rejected by strict inverse')
source('lean/MicroCFTA/SourcePruningEnumerationPrefixCompletion.lean',[(25,47)],'PrefixValid definition and exact retained counter field only')
source('lean/MicroCFTA/SourcePruningEnumerationPrefixCheckpointModels.lean',[(31,91)],'whole original theorem declaration recovered byte exactly; old proof body not claimed read here')
source('lean/MicroCFTA/SourcePruningEnumerationPreparedPrefixModels.lean',[(35,159)],'whole original theorem declaration recovered byte exactly; old proof body not claimed read here')
for name in ['source-validation.json','public-validation.json','audit-summary.json','public-blocks-index.json','source-head.txt','strict-checks.json','modules.json','document-inverse.json']:
 cp(area/name,'evidence/'+name)
v=json.loads((area/'source-validation.json').read_text());commands=[]
for row in v['commands']:
 d=area/row['folder'];r=json.loads((d/'report.json').read_text());b=(d/'raw.log').read_bytes()
 assert r['bytes']==row['bytes']==len(b) and r['sha256']==row['sha256']==sha(b) and r['exit_code']==row['exit_code']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for name in ['report.json','raw.log','inputs.json']:
  if (d/name).is_file():cp(d/name,'checks/'+row['folder']+'/'+name)
 for p in (d/'MicroCFTA').glob('*.lean'):
  cp(p,'checks/'+row['folder']+'/MicroCFTA/'+p.name)
 commands.append({'folder':row['folder'],'exit_code':row['exit_code'],'bytes':len(b),'sha256':sha(b),'inherited':row['folder']=='prior-public-readback'})
cp(area/'parent-v1/launch-failure.json','checks/parent-v1/launch-failure.json')
assert sum(not r['inherited'] for r in commands)==17
assert sum(not r['inherited'] and r['exit_code']!=0 for r in commands)==5
js('evidence/command-review.json',{'status':'PASS','current_actual_commands':17,'inherited_public_receipts':1,'failed_current_actual_commands':5,'precompiler_launch_failures':1,'records':commands,'scope':'Existing receipt, raw-byte/hash, exit and measured 4GiB/swap0 verification. No compiler/build/runtime was run by reviewer.'})
# Own source and both final prefix modules must equal the actual final strict snapshots.
for module,folder in [('SourcePruningEnumerationCheckedProjection','projection-v3'),('SourcePruningEnumerationPrefixCheckpointOrigins','prefix-v3'),('SourcePruningEnumerationPreparedPrefixOrigins','prepared-prefix-v2')]:
 b=(repo/'lean/MicroCFTA'/f'{module}.lean').read_bytes();s=(area/folder/'MicroCFTA'/f'{module}.lean').read_bytes();assert b==s
 assert sha(b)==v['source_hashes'][module]
# Eight full public blocks were read. Other owners retain the three large scan/receipt blocks.
blocks=[]
for r in json.loads((area/'public-blocks-index.json').read_text()):
 if r['name'].endswith('projectable') or r['name'].endswith('raw_ready_counterexample') or r['name'].endswith('assignment_origins') or r['name'].endswith('packet_prefix_complete_resources_origins') or r['name'].endswith('packet_prefix_preparation_complete_origins'):
  b=(area/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];assert b'propext' in b and b'Classical.choice' in b and b'Quot.sound' in b
  cp(area/r['path'],r['path']);blocks.append(r)
assert len(blocks)==8
full=(area/'public-readback-final/raw.log').read_bytes();old=(area/'prior-public-readback/raw.log').read_bytes();new=(area/'new-public-blocks.txt').read_bytes();assert full==old+new
for r in blocks:assert full.count((area/r['path']).read_bytes())==1
js('evidence/public-review.json',{'status':'PASS','whole_blocks_read':blocks,'whole_public_output_captured':True,'whole_public_output_read':False,'whole_new_appendix_read':False,'assigned_projection_blocks':5,'extra_prefix_blocks':3,'whole_read_bytes':sum(x['bytes'] for x in blocks),'old_exact_prefix_bytes':len(old),'full_bytes':len(full),'full_sha256':sha(full),'scope':'All five projection blocks and all three final prefix blocks read whole. Printed conjunction grouping reviewed; other three new blocks are assigned to other owners.'})
# Final docs: whole note and actual insertion texts; inverse equality for all old bodies.
note=repo/'lean/notes-current-prepared-composition.md';assert note.read_bytes()==(area/'root-review/notes-current-prepared-composition.md').read_bytes()
source('lean/notes-current-prepared-composition.md',[(1,len(note.read_bytes().splitlines()))],'whole final note read',dst='documents/notes-current-prepared-composition.md')
for name in ['common.md','findings.md']:cp(area/'document-insertions'/name,'documents/insertions/'+name)
records=[]
for rel,r in json.loads((area/'document-inverse.json').read_text()).items():
 b=(repo/rel).read_bytes();old=(area/'prior-documents'/rel).read_bytes();ins=(area/'document-insertions'/('findings.md' if rel=='FINDINGS.md' else 'common.md')).read_bytes()
 assert len(ins)==r['inserted_bytes'] and b.count(ins)==1
 at=b.index(ins);assert b[:at]+b[at+len(ins):]==old
 assert sha(b)==r['after_sha256'] and sha(old)==r['before_sha256']
 first=b[:at].count(b'\n')+1;last=first+len(ins.splitlines(keepends=True))-1
 assert b''.join(b.splitlines(keepends=True)[first-1:last])==ins
 cut=dict(save('documents/cuts/'+rel.replace('/','__')+'.inserted.txt',ins),first_line=first,last_line=last)
 idx['sources'].append({'source':str(repo/rel),'whole_identity':{'bytes':len(b),'sha256':sha(b)},'cuts':[cut],'inspected_scope':'exact insertion only; prior giant body checked by byte inverse, not read'})
 records.append({'source':str(repo/rel),'whole_bytes':len(b),'whole_sha256':sha(b),'prior_bytes':len(old),'prior_sha256':sha(old),'offset':at,'inserted_bytes':len(ins),'inserted_sha256':sha(ins),'exact_inverse':True,'read_scope':'whole insertion only'})
js('documents/document-verification.json',{'status':'PASS','whole_note':{'path':str(note),'bytes':note.stat().st_size,'sha256':sha(note.read_bytes())},'whole_common_and_findings_read':True,'records':records,'old_body_read_claim':False})
js('source-index.json',idx)
for r in idx['sources']:
 b=Path(r['source']).read_bytes();lines=b.splitlines(keepends=True)
 if 'whole' in r:
  w=r['whole'];assert (own/w['path']).read_bytes()==b and w['bytes']==len(b) and w['sha256']==sha(b)
 for c in r['cuts']:
  x=b''.join(lines[c['first_line']-1:c['last_line']]);assert (own/c['path']).read_bytes()==x and c['bytes']==len(x) and c['sha256']==sha(x)
print(json.dumps({'source_records':len(idx['sources']),'cuts':sum(len(r['cuts']) for r in idx['sources']),'note_bytes':note.stat().st_size,'note_sha256':sha(note.read_bytes()),'read_public_blocks':len(blocks),'read_public_bytes':sum(r['bytes'] for r in blocks)},indent=2))
