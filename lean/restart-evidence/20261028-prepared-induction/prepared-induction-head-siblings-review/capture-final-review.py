from pathlib import Path
import hashlib,json,shutil,datetime
A=Path('/tmp/mcfta-prepared-induction-20261028')
O=A/'prepared-induction-head-siblings-review'
R=Path('/home/tritlo/Code/mcfta')
assert not (O/'FROZEN.json').exists()
def sha(b): return hashlib.sha256(b).hexdigest()
def meta(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def save(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists(): assert p.read_bytes()==b, f'Immutable destination differs: {p}'
 else:p.write_bytes(b)
 return meta(p)
def cp(p,q):return save(q,p.read_bytes())
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
index=json.loads((O/'source-index.json').read_text())
def source(p,scope,cuts=()):
 b=p.read_bytes();h=sha(b)
 found=next((s for s in index['sources'] if s['source']==str(p) and s['whole']['sha256']==h),None)
 if not found:
  found={'source':str(p),'whole':save(O/'sources'/f'{p.name}.{h[:12]}.whole',b),'cuts':[],'read_scope':scope}
  index['sources'].append(found)
 lines=b.splitlines(keepends=True)
 for first,last in cuts:
  bb=b''.join(lines[first-1:last]);q=O/'cuts'/f'{p.name}.{h[:12]}.L{first}-L{last}.txt'
  rec={**save(q,bb),'first_line':first,'last_line':last}
  if rec not in found['cuts']:found['cuts'].append(rec)
 return found
# Preserve current root metadata. These are evidence inputs, not new executions.
for n in ['modules.json','strict-checks.json','source-head.txt','source-commits.json','published-base.txt','source-validation.json','preservation-validation.json','public-validation.json','new-public-block-index.json','new-public-declarations.json','public-definitions.json','public-declarations.json','actual-commands.json','document-validation.json','document-paths.json','audit-import-insertion.json']:
 p=A/n;cp(p,O/'final-evidence'/n)
 source(p,'Whole metadata input read or identity/status checked; does not assert review of every referenced proof.')
# Retain and validate all current command reports, raw logs and exact Lean snapshots.
commands=json.loads((A/'actual-commands.json').read_text());assert len(commands)==49
checked=[]
for item in commands:
 name=item['name'];base=A/name;report=json.loads((base/'report.json').read_text());raw=(base/'raw.log').read_bytes()
 assert report==item['report']
 assert len(raw)==report['bytes'] and sha(raw)==report['sha256']
 lim=report['cgroup_limits'];assert lim['memory.max']==lim['memory.high']=='4294967296' and lim['memory.swap.max']=='0'
 for p in [base/'report.json',base/'raw.log',*sorted(base.rglob('*.lean'))]:cp(p,O/'evidence'/name/p.relative_to(base))
 checked.append({'name':name,'exit_code':report['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'limits':lim,'report':str(O/'evidence'/name/'report.json'),'source_snapshots':[str(q.relative_to(base)) for q in sorted(base.rglob('*.lean'))]})
assert sum(c['exit_code']!=0 for c in checked)==7
# Final checked sources must match current installed bytes and exact strict snapshots.
sv=json.loads((A/'source-validation.json').read_text())
assert sv['status']=='pass'
for item in sv['strict_checks']:
 p=R/'lean/MicroCFTA'/f"{item['module']}.lean"
 assert p.stat().st_size==item['bytes'] and sha(p.read_bytes())==item['sha256']
 snap=A/item['check']/'MicroCFTA'/p.name
 assert snap.read_bytes()==p.read_bytes()
 source(p,'Installed final source identity checked. Whole proof review is limited to the separately stated owned/integration modules.')
# Public prior prefix and complete reviewed declarations.
pub=A/'public-readback-final/raw.log';old=A/'prior-public-readback/raw.log';append=A/'new-public-blocks.txt'
pv=json.loads((A/'public-validation.json').read_text())
assert pub.read_bytes()==old.read_bytes()+append.read_bytes()
assert sha(pub.read_bytes())==pv['sha256'] and len(pub.read_bytes())==pv['bytes']
for p in [pub,old,A/'public-readback-final/public.lean',A/'public-readback-final/report.json']:
 source(p,'Whole preserved public artifact. Semantic read scope is the explicit complete selected blocks and definitions prefix; old output is checked as exact bytes, not reread in full.')
 cp(p,O/'final-evidence'/p.relative_to(A))
blocks=json.loads((A/'new-public-block-index.json').read_text());selected=[52,53,54,55,56,57,59,61,62,63,64]
bb=append.read_bytes();defs=bb[:blocks[0]['byte_start']];assert len(defs)==19233
save(O/'final-public'/'definitions-prefix.txt',defs)
read_blocks=[]
for n in selected:
 info=blocks[n-1];p=Path(info['path']);b=p.read_bytes()
 assert b==bb[info['byte_start']:info['byte_end_exclusive']] and len(b)==info['bytes'] and sha(b)==info['sha256']
 cp(p,O/'final-public'/p.name)
 source(p,'WHOLE complete printed theorem and axiom block read, with no elision.',[(1,len(b.splitlines()))])
 read_blocks.append(info)
source(append,'WHOLE artifact retained. Read complete definitions prefix and eleven complete blocks listed in final-public-review.json; no claim to all 64 theorem blocks.',[(1,len(defs.splitlines()))])
# All nine current insertions and exact inverse old bytes. Old document bodies were not semantically reread.
docs=json.loads((A/'document-validation.json').read_text());inverse=[]
common=(A/'document-common-insertion.txt').read_bytes();findings=(A/'document-findings-insertion.txt').read_bytes()
for n in ['document-common-insertion.txt','document-findings-insertion.txt']:
 p=A/n;source(p,'WHOLE exact new insertion text read.',[(1,len(p.read_bytes().splitlines()))]);cp(p,O/'final-documents'/n)
for d in docs:
 p=R/d['path'];b=p.read_bytes();assert len(b)==d['bytes'] and sha(b)==d['sha256']
 if 'inserted_bytes' not in d:
  assert len(b)==13272 and sha(b)=='45149541b7c41ae719d12ad8874f59786b7366a5e91fcd43773c02420edeafbf'
  source(p,'WHOLE new note read.',[(1,len(b.splitlines()))]);cp(p,O/'final-documents'/d['path']);continue
 offset=d['offset'];size=d['inserted_bytes'];ins=b[offset:offset+size];prior=b[:offset]+b[offset+size:]
 assert ins==(findings if d['path']=='FINDINGS.md' else common)
 assert len(prior)==d['prior_bytes'] and sha(prior)==d['prior_sha256']
 pp=A/'prior-documents'/d['path'];assert pp.read_bytes()==prior
 current_meta=cp(p,O/'final-documents/current'/d['path']);prior_meta=cp(pp,O/'final-documents/prior'/d['path'])
 insert_meta=save(O/'final-documents/insertions'/(d['path'].replace('/','--')+'.txt'),ins)
 first=b[:offset].count(b'\n')+1;last=first+len(ins.splitlines())-1
 # These insertions start and end at line boundaries.
 assert b''.join(b.splitlines(keepends=True)[first-1:last])==ins
 source(p,'ONLY exact current insertion reviewed semantically. Whole current document retained for inverse identities; old giant body was not reread.',[(first,last)])
 source(pp,'Exact prior-body bytes retained and inverse-checked; no whole-body semantic review claimed.')
 inverse.append({'source':str(p),'offset':offset,'current':current_meta,'prior':prior_meta,'insert':insert_meta,'inverse_exact':True})
assert len(inverse)==9
# Own final source identities remain exact immutable variants.
owned={
 'PreparedFiniteHeadResources':('drafts/v2','34bfa6cd1cc06fef2269b33a4efb28bed13756561457af2c492f516ac326d0b2'),
 'PreparedFiniteSiblingCertificates':('drafts/v2','8bd118235c9b75bd5d3aec4c9c7c59dc9b2c9aa61b72c24dbc2d9c41b4dd4d06'),
 'PreparedFiniteSiblingResources':('drafts/v2','dac763a18d72f6dd54fdca3c2a9716079bc8dca823eaebd0aa6c554be82d71b6'),
 'PreparedFiniteSiblingFinishResources':('drafts/v2','6f25732227069dc73e66d9aeaafeb212c7b7c19fee7879575c52609ef4093333'),
 'PreparedOrdinaryResources':('drafts/ordinary-v3','a358e1117f4c07af884f01f1de94f39e7cb6d29a307871d89bf590309dee8c0b')}
for suffix,(variant,h) in owned.items():
 p=R/'lean/MicroCFTA'/f'SourcePruningEnumeration{suffix}.lean';assert sha(p.read_bytes())==h
 assert (O/variant/p.name).read_bytes()==p.read_bytes()
dump(O/'source-index.json',index)
dump(O/'final-command-identities.json',{'commands':checked,'command_count':49,'failures':7,'execution_owner':'Root; this reviewer did not run Lean, builds, native code, Git or network','raw_read_scope':'Final owned and integration source proofs, final aggregate/strict-Audit log, public blocks and metadata read. All failure bytes/snapshots retained and hash-checked. This reviewer does not claim to have read every large historical failed log; Root reports that complete read.'})
dump(O/'document-inverse-checks.json',{'documents':inverse,'status':'pass','semantic_scope':'Whole new note and all nine insertion texts; prior bodies only byte-preserved and inverse-checked.'})
dump(O/'final-public-review.json',{'status':'CLEAR','definitions_prefix_bytes':19233,'definitions_prefix_sha256':sha(defs),'whole_theorem_blocks_read':read_blocks,'all_new_theorem_blocks':64,'all_new_blocks_read':False,'old_prefix_bytes':len(old.read_bytes()),'public':meta(pub),'new_appendix':meta(append)})
dump(O/'final-review-status.json',{'status':'CLEAR; OPEN awaiting Root seal cue','source_head':(A/'source-head.txt').read_text().strip(),'owned_modules':list(owned),'source_records':len(index['sources']),'literal_cuts':sum(len(s['cuts']) for s in index['sources']),'timestamp':datetime.datetime.now().astimezone().isoformat(),'note_sha256':'45149541b7c41ae719d12ad8874f59786b7366a5e91fcd43773c02420edeafbf'})
print(json.dumps({'status':'capture PASS; remains OPEN','sources':len(index['sources']),'cuts':sum(len(s['cuts']) for s in index['sources']),'commands':49,'failures':7,'documents':9,'public_blocks_read':len(read_blocks)},indent=2))
