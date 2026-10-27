from pathlib import Path
import hashlib,json,re,shutil,datetime
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-admission-20261027');base=area/'claim-review'
assert not (base/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest();now=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
for d in ['sources','cuts','documents','evidence','public-cuts']: (base/d).mkdir(parents=True,exist_ok=True)
validation=json.loads((area/'source-validation.json').read_text());docs=json.loads((area/'document-validation.json').read_text());pub=json.loads((area/'public-validation.json').read_text())
cut_specs={
 'SourcePruningEnumerationOrdinaryInvocationResources':[(41,185),(189,279)],
 'SourcePruningEnumerationFiniteCallbackReceiptLanguage':[(41,71),(74,157),(160,213)],
 'SourcePruningEnumerationIsolationReads':[(20,90)],
 'SourcePruningEnumerationOrdinaryIsolationResources':[(41,122)],
 'SourcePruningEnumerationOrdinaryReceiptLanguage':[(28,90),(93,157)],
 'SourcePruningEnumerationOrdinaryInvocationLanguage':[(39,156),(157,204)],
 'SourcePruningEnumerationSelectedReceiptLanguage':[(62,137),(138,170)],
 'SourcePruningEnumerationCapturedIsolation':[(60,144)],
 'SourcePruningEnumerationCallbackAdmission':[(30,46),(52,77),(113,195)],
}
records=[];strict=[];line_count=theorem_count=structure_count=0
for row in validation['strict_checks']:
 module=row['module'];p=repo/'lean/MicroCFTA'/(module+'.lean');b=p.read_bytes();e=area/row['check'];snap=e/'MicroCFTA'/p.name;r=json.loads((e/'report.json').read_text());raw=(e/'raw.log').read_bytes()
 assert b==snap.read_bytes() and len(b)==row['bytes'] and sha(b)==row['sha256']==r['source_sha256']
 assert r['exit_code']==0 and len(raw)==r['bytes'] and sha(raw)==r['sha256']
 if module!='Audit': assert not raw
 else: assert raw==b'Checked axiom dependencies of 79370 MicroCFTA theorems.\n'
 dest=base/'evidence'/row['check'];dest.mkdir(exist_ok=True)
 for f in ['report.json','raw.log']:shutil.copyfile(e/f,dest/f)
 shutil.copyfile(snap,dest/p.name)
 strict.append({'module':module,'check':row['check'],'source_sha256':sha(b),'exit_code':0,'raw_bytes':len(raw)})
 if module=='Audit': continue
 t=b.decode();line_count+=len(b.splitlines());theorem_count+=len(re.findall(r'^theorem ',t,re.M));structure_count+=len(re.findall(r'^structure ',t,re.M))
 q=base/'sources'/p.name;q.write_bytes(b)
 rec={'source':str(p),'snapshot':str(q),'scope':'whole source','reviewed_scope':'whole, with earlier sealed detailed source reviews where unchanged','bytes':len(b),'sha256':sha(b),'line_count':len(b.splitlines()),'cuts':[]}
 for f,l in cut_specs[module]:
  cut=b''.join(b.splitlines(keepends=True)[f-1:l]);out=base/'cuts'/f'{module}.{f}-{l}.txt';out.write_bytes(cut)
  rec['cuts'].append({'scope':'literal source cut','first_line':f,'last_line':l,'snapshot':str(out),'bytes':len(cut),'sha256':sha(cut)})
 records.append(rec)
assert (len(records),line_count,theorem_count,structure_count)==(9,1592,16,2)
inverses=[];regions=[]
for row in docs:
 p=repo/row['path'];b=p.read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256']
 if 'offset' not in row:
  assert p.name=='notes-current-recursive-admission.md';q=base/'documents'/p.name;q.write_bytes(b)
  assert b'head_mass_le bounds the actual mass by massCeil.' in b
  records.append({'source':str(p),'snapshot':str(q),'scope':'whole note','reviewed_scope':'whole','bytes':len(b),'sha256':sha(b),'cuts':[]});continue
 off=row['offset'];size=row['inserted_bytes'];region=b[off:off+size];regions.append(region)
 oldp=area/'prior-documents'/row['path'];old=oldp.read_bytes();restored=b[:off]+b[off+size:];assert restored==old
 first=len(b[:off].splitlines(keepends=True))+1;last=first+len(region.splitlines(keepends=True))-1
 assert b''.join(b.splitlines(keepends=True)[first-1:last])==region
 q=base/'documents'/(row['path'].replace('/','__')+'.status-cut.txt');q.write_bytes(region)
 cut={'scope':'literal inserted status cut','first_line':first,'last_line':last,'byte_offset':off,'snapshot':str(q),'bytes':len(region),'sha256':sha(region)}
 records.append({'source':str(p),'scope':'whole live identity only; reviewed snapshot is the labeled inserted cut','reviewed_scope':'listed status cut only; unchanged historical body not reread','bytes':len(b),'sha256':sha(b),'cuts':[cut]})
 inverses.append({'source':str(p),'current_bytes':len(b),'current_sha256':sha(b),'removed_byte_offset':off,'removed_bytes':size,'removed_sha256':sha(region),'prior_source':str(oldp),'prior_bytes':len(old),'prior_sha256':sha(old),'restored_sha256':sha(restored),'exact_prior_equality':True})
assert len(regions)==9 and len(set(regions))==1
(base/'document-inverses.json').write_text(json.dumps({'created':now,'status':'9 exact inverses PASS','records':inverses},indent=2)+'\n')
(base/'source-index.json').write_text(json.dumps({'created':now,'cut_convention':'One-based inclusive line bounds. Literal bytes are splitlines(keepends=True)[first_line-1:last_line], with trailing LF. Whole live identities have snapshots only when a whole copy exists. A status-cut snapshot is never labeled a whole document copy.','sources':records},indent=2)+'\n')
# Retain exact validation and actual terminal evidence.
for f in ['source-validation.json','public-validation.json','document-validation.json','document-paths.json','strict-checks.json','public-declarations.json','public-definitions.json']:shutil.copyfile(area/f,base/'evidence'/f)
for family in ['build-aggregate-final','public-readback-final-1']:
 d=base/'evidence'/family;d.mkdir(exist_ok=True)
 for f in ['report.json','raw.log']:shutil.copyfile(area/family/f,d/f)
 report=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes();assert report['exit_code']==0 and report['bytes']==len(raw) and report['sha256']==sha(raw)
 if family=='public-readback-final-1':
  shutil.copyfile(area/family/'public.lean',d/'public.lean');assert report['source_sha256']==sha((d/'public.lean').read_bytes())
aggregate=(area/'build-aggregate-final/raw.log').read_text();assert '79370 MicroCFTA theorems' in aggregate and '4121 jobs' in aggregate
raw=(area/'public-readback-final-1/raw.log').read_bytes();assert len(raw)==pub['bytes']==185873 and sha(raw)==pub['sha256'];text=raw.decode()
sets=re.findall(r'depends on axioms: \[([^]]*)\]',text,re.S);union=sorted({x.strip() for s in sets for x in s.split(',')});assert len(sets)==19 and union==['Classical.choice','Quot.sound','propext'];assert not re.search(r'⋯|…|\.\.\.',text)
priorpath=Path('/tmp/mcfta-recursive-receipts-20261027/public-readback-final-1/raw.log');prior=priorpath.read_text();priorcuts=[]
for name in pub['unchanged_prior_signatures']:
 def block(s):
  start=re.search(r'^MicroCFTA\.'+re.escape(name)+r'(?=\s)',s,re.M).start();mark="'MicroCFTA."+name+"' depends on axioms: [";end=s.index(']',s.index(mark,start))+1;return s[start:end],start,end
 current,start,end=block(text);earlier,_,_=block(prior);assert current==earlier
 out=base/'public-cuts'/(name+'.txt');out.write_bytes(current.encode())
 priorcuts.append({'scope':'literal printed signature and axiom block','source':str(area/'public-readback-final-1/raw.log'),'source_sha256':sha(raw),'byte_offset':len(text[:start].encode()),'snapshot':str(out),'bytes':len(current.encode()),'sha256':sha(current.encode()),'prior_source':str(priorpath),'prior_source_sha256':sha(prior.encode()),'exact_prior_block_equality':True})
(base/'public-comparison.json').write_text(json.dumps({'created':now,'public_bytes':185873,'public_sha256':sha(raw),'printed_signature_axiom_blocks':19,'new_theorems':16,'structures':2,'axioms':union,'no_elision':True,'prior_blocks':priorcuts,'review_scope':'Whole raw custody/hash/count/axiom and exact old-block checks; source contracts and current documentation claims reviewed. No claim of a new line-by-line review of all 185873 printed bytes.'},indent=2)+'\n')
report=f'''[{now}] CLEAR — final recursive-admission checkpoint claims.

Reviewed the WHOLE current note and all nine new status cuts. Source checkpoint is recorded as fcbb20ee93aacabb645c09cf5e64ff08be86c23f. The corrected note is 12276 bytes, SHA256 f93f49d387f0fbe56cd2c0a49e2c9f2d878b7b90f4e9897391d984f2a1d0ee9f. The mass wording now states a bound by massCeil. Nine identical 1689-byte inserted regions have SHA256 ed9ed2122496df1e8674121710598bd54aa3a1b25d67086eb4e724600b0cf7e2. Removing each insertion restores the exact preserved prior document bytes. document-inverses.json records all nine old/restored hashes. Historical document bodies were not reread; their review snapshots are explicitly labeled cuts.

Scope is accurate. The strongest new selected-step law consumes actual PrefixValid, actual narrowed execution, actual entry, completed-head and false-callback observations. It is conditional on the stated Canonical, nonterminal, fresh-arity and structural retention gates. It restores original selected-cache satisfaction at the original native heap, with local edge/parent acceptance, inherited Holds and fill equality. The original selected variable and actual ordinary target remain distinct parameters. No receipt producer for every recursive OutputHistory tag is claimed.

The ordinary producer retains its full previous execution, Post/full Memos/resource and stop/output packet. Its appended law interprets each actual invocation under explicit structural gates; those gates are not new initial resource admission. Each sibling uses the same captured entered cache and actual post-hook native Caller/full Memos. Entry ancestry is handled separately and is not called a full Frame. The callback local iff concerns only its actual returned core at its unchanged native heap; it does not interpret the later recursive output.

Isolation claims stay local. Actual successful entry and either callback side/result preserve the isolated slot. Ordinary isolation concerns the entered cache. CompletedHeadReceipt.isolated protects a different held slot at the actual completed capture and needs neither universal Ranges nor semantic acceptance gates. It does not imply whole-history isolation or equate Done with Discharged.

The new RecursiveCallbackAdmission exports the original callback seed, mass ceiling, Fits/guard carrier, allocation and reservation. The head wrapper retains every old binder/witness/field, with only explicit grouping of its old final universal field, and calls the old head producer once. Its after_false transport keeps the exact returned Packet and original seed/ceiling/reservation. The note correctly states that the new admission is NOT yet lifted into older sibling/ordinary receipt families. A stronger depth IH must choose its own common work bound before all actual larger-fuel observations. Desired satisfaction, future success and final invariants are not new producer admission.

Validation matches actual retained evidence. Nine installed modules total 1592 lines, 16 theorem declarations and two structures. Their actual successful strict source snapshots match all current bytes and have empty logs. Audit strict passes with its 56-byte dependency summary. The aggregate passes 4121 jobs and 79370 dependency checks and retains the earlier dependency warning. Reports use Lean 4.34.1, warnings fatal/all linters, 4 GiB memory.max/high and swap 0. Public output is 185873 bytes, SHA256 e9d846f4ad95a0d6c30c1f94d2033172efe6c9e2a25a4c4e8ec29cce6253f03b, with 19 signature/axiom blocks and two structures, no elision, and only Classical.choice, Quot.sound and propext. H6 and both prior captured renderer signature/axiom blocks are literally identical to the prior readback. H6 remains the global construction boundary.

No Haskell change or new Haskell defect is claimed. Prior repair handoffs, opaque Mu/Union limits and unexecuted recipe status remain explicit. Whole recursive acceptance, coverage, ancestry/loss discharge, original resource admission at every history tag and physical Haskell correspondence remain open. Canonical storage does not recover dropped suspended constraints.

Publication scope. The note states future publication requirements. This review does not assert that a new portable archive, committed-byte check, seal or push has already occurred. Root must create/verify the portable snapshot and run --committed before publication. No builds, Git/network actions, repository edits or earlier sealed bundle changes were performed for this review. Evidence includes exact current source/strict snapshots, source cuts, the full corrected note, explicitly labeled status cuts, actual reports/logs, public output and inverse/hash checks.
'''
(base/'report.txt').write_text(report)
(base/'review-summary.json').write_text(json.dumps({'created':now,'status':'CLEAR','source_checkpoint_recorded':'fcbb20ee93aacabb645c09cf5e64ff08be86c23f','source_modules':9,'source_lines':1592,'new_theorems':16,'structures':2,'strict_checks':strict,'document_inverses':9,'status_cut_sha256':sha(regions[0]),'note_sha256':sha((repo/'lean/notes-current-recursive-admission.md').read_bytes()),'publication_verification':'required after report; not claimed completed','report_sha256':sha(report.encode())},indent=2)+'\n')
# Final source/document/cut check before sealing.
for rec in records:
 b=Path(rec['source']).read_bytes();assert len(b)==rec['bytes'] and sha(b)==rec['sha256']
 if 'snapshot' in rec:assert Path(rec['snapshot']).read_bytes()==b
 for c in rec['cuts']:
  cut=b''.join(b.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert cut==Path(c['snapshot']).read_bytes() and sha(cut)==c['sha256']
files=sorted(p for p in base.rglob('*') if p.is_file() and p.name not in ['pins.json','FROZEN.json'])
pins={'created':now,'files':{str(p.relative_to(base)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files}}
(base/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
frozen={'created':now,'status':'FROZEN / CLEAR','payload_count':len(files),'exact_file_count':len(files)+2,'pins_sha256':sha((base/'pins.json').read_bytes()),'report_sha256':sha((base/'report.txt').read_bytes()),'source_index_sha256':sha((base/'source-index.json').read_bytes()),'note_sha256':sha((repo/'lean/notes-current-recursive-admission.md').read_bytes())}
(base/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
for rel,r in pins['files'].items(): b=(base/rel).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
assert len([p for p in base.rglob('*') if p.is_file()])==frozen['exact_file_count']
print(json.dumps({'area':str(base),'payload_count':len(files),'exact_file_count':len(files)+2,'FROZEN_sha256':sha((base/'FROZEN.json').read_bytes()),**{k:frozen[k] for k in ['pins_sha256','report_sha256','source_index_sha256','note_sha256']}},indent=2))
