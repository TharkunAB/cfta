from pathlib import Path
import hashlib,json,re,subprocess
A=Path('/tmp/mcfta-enumeration-startup-20261027');R=Path('/home/tritlo/Code/mcfta');D=A/'independent-review'
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_text())
def save(rel,b):p=D/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
records=j(D/'source-pins-current.json')['sources']
def copy(p,rel,scope):
 b=p.read_bytes();save(rel,b);x={'source_path':str(p),'copy':rel,'bytes':len(b),'sha256':sha(b),'review_scope':scope};records.append(x);return x
# Revalidate the final installed source against both immutable drafts and actual strict snapshots.
mods=j(A/'modules.json');current=[]
for m in mods:
 p=R/'lean/MicroCFTA'/f'{m}.lean';b=p.read_bytes();assert b==(D/'drafts'/p.name).read_bytes()
 cn={'SourcePruningEnumerationInitialPacket':'strict-initial-packet-1','SourcePruningEnumerationInitialRendering':'strict-initial-rendering-1'}[m]
 assert b==(A/cn/'MicroCFTA'/p.name).read_bytes();copy(p,'installed/'+p.name,'Whole final source read; installed/draft/strict bytes identical')
 current.append({'module':m,'bytes':len(b),'lines':len(b.splitlines()),'sha256':sha(b)})
assert sum(x['lines'] for x in current)==198 and sum(x['bytes'] for x in current)==12669
# Public block comparison ends at each complete axiom set, excluding unrelated trailing output.
raw=(A/'public-readback-1/raw.log').read_bytes();oldraw=(A/'prior-public-readback/raw.log').read_bytes();names=j(A/'public-declarations.json');prior=j(A/'prior-public-declarations.json')
def blocks(b,names):
 pattern=re.compile(rb'^MicroCFTA\.('+b'|'.join(re.escape(x.encode()) for x in names)+rb')(?=\s|\{)',re.M);out={}
 for m in pattern.finditer(b):
  name=m.group(1).decode();tail=b[m.start():];end=re.search(rb"'MicroCFTA\."+re.escape(name.encode())+rb"' depends on axioms: \[[^\]]*\]\n",tail);assert end
  block=tail[:end.end()];start=b[:m.start()].count(b'\n')+1;out[name]=(start,start+len(block.splitlines())-1,block)
 assert len(out)==len(names);return out
B=blocks(raw,names);O=blocks(oldraw,prior);assert len(B)==159 and len(O)==157
for n in prior:assert B[n][2]==O[n][2],n
axs=re.findall(rb"'MicroCFTA\.[^']+' depends on axioms: \[([^\]]*)\]",raw);assert len(axs)==159
for ax in axs:assert set(x.strip() for x in ax.decode().split(','))<={'propext','Classical.choice','Quot.sound'}
assert len(raw)==539153 and sha(raw)=='a2bd227d4d5d8e123572c1b0efd409f46b27530c41752295b59bd9524ada1a84'
assert b'...' not in raw and b'\xe2\x80\xa6' not in raw
new=['SourcePruningEnumerationRecursive.initial_packet','SourcePruningEnumerationRecursive.run_initial_finite_render_sound']
# Retain actual success/failure receipts, not a rerun by this reviewer.
checks=[]
for cn in ['public-readback-1','prior-public-readback','audit-startup-1','audit-startup-2','strict-audit-startup-1']:
 rp=A/cn/'report.json';report=j(rp);b=(A/cn/'raw.log').read_bytes();assert len(b)==report['bytes'] and sha(b)==report['sha256'] and report['exit_code']==(1 if cn=='audit-startup-1' else 0)
 if cn!='prior-public-readback':
  for field in ['memory.max','memory.high']:assert report['cgroup_limits'][field]=='4294967296'
  assert report['cgroup_limits']['memory.swap.max']=='0'
 for p in sorted((A/cn).rglob('*')):
  if p.is_file():copy(p,'evidence/'+cn+'/'+str(p.relative_to(A/cn)),'Actual Root source/report/raw; failed Audit import placement explicitly retained')
 checks.append({'check':cn,'exit_code':report['exit_code'],'raw_bytes':len(b),'raw_sha256':sha(b)})
pub=next(x for x in records if x['copy']=='evidence/public-readback-1/raw.log');pub['cuts']=[]
for i,n in enumerate(new):
 first,last,b=B[n];rel=f'public-blocks/{i+1}-{n.rsplit(".",1)[-1]}.txt';save(rel,b);pub['cuts'].append({'path':rel,'start_line':first,'end_line':last,'bytes':len(b),'sha256':sha(b),'declaration':n,'review_scope':'Complete installed signature and axiom set read'})
# Prior source preservation is a bounded hash check, not rereading all eighty proofs.
old_sources=[]
for x in j(A/'prior-strong-sources.json'):
 b=(R/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];old_sources.append(x)
assert len(old_sources)==80
# Both final import lines remove exactly to the original Audit bytes.
audit=(R/'lean/MicroCFTA/Audit.lean').read_bytes();undo=audit
for m in mods:
 line=f'import MicroCFTA.{m}\n'.encode();assert undo.count(line)==1;undo=undo.replace(line,b'',1)
old=(A/'prior-sources/Audit.lean').read_bytes();assert undo==old
copy(R/'lean/MicroCFTA/Audit.lean','inputs/Audit-final.lean','Only new import placement and exact old-byte inverse checked')
copy(A/'prior-sources/Audit.lean','inputs/Audit-prior.lean','Original bytes for import inverse')
assert b'4234 jobs' in (A/'audit-startup-2/raw.log').read_bytes() and b'80044' in (A/'strict-audit-startup-1/raw.log').read_bytes()
# Full new note and all nine exact new insertions. Older large prose is checked by inverse, not recopied or reread.
docs=[]
for x in j(A/'document-validation.json'):
 p=R/x['path'];b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 if 'offset' in x:
  o=x['offset'];n=x['inserted_bytes'];region=b[o:o+n];old=(A/'prior-documents'/x['path']).read_bytes();assert b[:o]+b[o+n:]==old
  rel='document-insertions/'+x['path'];save(rel,region);docs.append({'document_source_path':str(p),'whole_bytes':len(b),'whole_sha256':sha(b),'region_copy':rel,'offset':o,'inserted_bytes':n,'region_sha256':sha(region),'prior_bytes':len(old),'prior_sha256':sha(old),'inverse_byte_exact':True,'review_scope':'Full new region read; old prose preserved by inverse only'})
 else:
  copy(p,'documents/'+x['path'],'Whole new final note read, including corrected strict-check wording')
  docs.append({'document_source_path':str(p),'whole_bytes':len(b),'whole_sha256':sha(b),'review_scope':'Whole new final note read'})
assert len(docs)==10 and sum('inverse_byte_exact'in x for x in docs)==9
note=next(x for x in docs if 'inverse_byte_exact'not in x);assert note['whole_bytes']==8591 and note['whole_sha256']=='dfd22f6890dd33689d5626360009f15ec14b41c0a24ef837efacbebf39a62e24'
# No external helper pin is introduced.
for rel in ['source-validation.json','public-validation.json','statistics.json','modules.json','public-declarations.json','prior-public-declarations.json','public-definitions.json','prior-strong-sources.json','source-head.txt','source-commit.json','audit-import-placement-repair.json','document-validation.json','document-paths.json']:
 copy(A/rel,'root-evidence/'+rel,'Root provenance retained; relevant identities independently checked')
independent={'status':'PASS','source_head':(A/'source-head.txt').read_text().strip(),'current_sources':current,'prior_source_count':len(old_sources),'prior_sources_byte_exact':old_sources,'all_public_blocks':159,'new_complete_public_blocks_read':new,'prior_public_blocks_byte_exact':157,'public_bytes':len(raw),'public_sha256':sha(raw),'axioms':['propext','Classical.choice','Quot.sound'],'audit_old_bytes_exact_after_two_imports':True,'actual_checks':checks,'documents':docs,'reviewer_ran_checks':False}
save('final-independent-validation.json',(json.dumps(independent,indent=2)+'\n').encode());save('source-pins-final.json',(json.dumps({'sources':records},indent=2)+'\n').encode())
# Validate all retained source copies and every literal source/public cut before sealing.
for x in records:
 b=(D/x['copy']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];assert Path(x['source_path']).read_bytes()==b,x['source_path']
 for c in x.get('cuts',[]):
  cut=(D/c['path']).read_bytes();assert 1<=c['start_line']<=c['end_line']<=len(b.splitlines()),c['path'];assert cut==b''.join(b.splitlines(keepends=True)[c['start_line']-1:c['end_line']]);assert len(cut)==c['bytes'] and sha(cut)==c['sha256']
print(json.dumps({'status':'FINAL REVIEW ASSEMBLED AND VERIFIED; NOT YET SEALED','records':len(records),'literal_cuts':sum(len(x.get('cuts',[])) for x in records),'prior_public':157,'prior_sources':80,'doc_inverses':9,'files':len([p for p in D.rglob('*') if p.is_file()])},indent=2))
