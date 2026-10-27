from pathlib import Path
import datetime,hashlib,json,re
B=Path('/tmp/mcfta-worker-arity-20261027/parent-arity'); A=B.parent; P=A/'public-readback-final-1'; repo=Path('/home/tritlo/Code/mcfta')
assert not(B/'FROZEN').exists()
H=lambda b:hashlib.sha256(b).hexdigest()
def capture(p,dest):
 data=p.read_bytes();dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists(): assert dest.read_bytes()==data,(p,dest)
 else:dest.write_bytes(data)
 return data
# Retain final source identities, readback inputs, strict output and the actual aggregate.
for source in [P/'raw.log',P/'public.lean',P/'report.json',A/'public-validation.json',A/'source-validation.json',A/'modules.json',A/'strict-checks.json']:
 rel=Path('final-integration')/(('public-'+source.name) if source.parent==P else source.name)
 capture(source,B/rel)
for group in ['build-audit-1','strict-audit-1']:
 report=json.loads((A/group/'report.json').read_text());raw=(A/group/'raw.log').read_bytes()
 assert report['exit_code']==0 and report['bytes']==len(raw) and report['sha256']==H(raw)
 for rel in ['report.json','raw.log']:capture(A/group/rel,B/'final-integration'/group/rel)
public_raw=(P/'raw.log').read_bytes();public_report=json.loads((P/'report.json').read_text())
assert public_report['exit_code']==0 and public_report['bytes']==len(public_raw) and public_report['sha256']==H(public_raw)
assert H(public_raw)=='7119d146f5780ab89cb0d2bfcc3cdb8e894401cc41abf4b94c67e4f308b8771b'
lines=public_raw.splitlines(keepends=True)
starts=[i for i,l in enumerate(lines) if re.match(rb'^(?:MicroCFTA\.|structure MicroCFTA\.|def MicroCFTA\.)',l)]
blocks={}
for ix,first in enumerate(starts):
 end=starts[ix+1] if ix+1<len(starts) else len(lines)
 match=re.match(rb'^(?:(?:structure|def) )?(MicroCFTA\.[^\s{(:]+)',lines[first]);assert match
 blocks[match[1].decode()]=(first,end,b''.join(lines[first:end]))
names=['MicroCFTA.SourcePruningEnumerationClassEditArity.'+n for n in ['node_heap','children_heap','rows_heap','list_heap','class_heap','fold_heap','pass_heap']]
names+=['MicroCFTA.SourcePruningEnumerationLocalReductionArity.'+n for n in ['reduction_heap','literal_heap']]
names+=['MicroCFTA.SourcePruningEnumerationParentArity.parent_heap']
public_cuts=[]
for name in names:
 first,end,data=blocks[name];assert ("'"+name+"' depends on axioms:").encode() in data
 ax=data.split(b'depends on axioms:')[1]
 assert set(re.findall(rb'\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b',ax))=={b'propext',b'Classical.choice',b'Quot.sound'}
 assert b'sorryAx' not in ax
 dest=B/'final-public-blocks'/(name+'.txt');dest.parent.mkdir(exist_ok=True);dest.write_bytes(data)
 public_cuts.append({'first_line':first+1,'last_line':end,'snapshot':str(dest),'bytes':len(data),'sha256':H(data),'scope':'complete installed public theorem signature and axioms','purpose':name})
# Literal declarations from the four full reviewed final modules.
source_records=[]
checked=json.loads((B/'checked-sources.json').read_text())
for record in checked:
 data=(B/record['snapshot']).read_bytes();p=repo/record['installed_source'];assert p.read_bytes()==data
 cuts=[];textlines=data.splitlines(keepends=True)
 if record['module']!='SourcePruningEnumerationSharedTargetArity':
  for i,line in enumerate(textlines):
   m=re.match(rb'^theorem (\w+)',line)
   if not m:continue
   end=i
   while b':=' not in textlines[end]:end+=1
   piece=b''.join(textlines[i:end+1]);dest=B/'final-source-cuts'/(record['module']+'.'+m[1].decode()+'.txt');dest.parent.mkdir(exist_ok=True);dest.write_bytes(piece)
   cuts.append({'first_line':i+1,'last_line':end+1,'snapshot':str(dest),'bytes':len(piece),'sha256':H(piece),'scope':'exact complete public declaration through proof start'})
 source_records.append({'source':str(p),'snapshot':str(B/record['snapshot']),'bytes':len(data),'sha256':H(data),'scope':'WHOLE final checked source; reviewed proof and header','cuts':cuts})
# Keep the bounded original source copies and their literal used spans.
old=json.loads((B/'source-pins.json').read_text())
for record in old['whole_files']:
 data=(B/record['snapshot']).read_bytes();src=repo/record['source'];assert src.read_bytes()==data
 cuts=[]
 for cut in old.get('cuts',[]):
  if cut['source']!=record['source']:continue
  piece=b''.join(data.splitlines(keepends=True)[cut['start_line']-1:cut['end_line']]);dest=B/cut['snapshot'];assert dest.read_bytes()==piece and H(piece)==cut['sha256']
  cuts.append({'first_line':cut['start_line'],'last_line':cut['end_line'],'snapshot':str(dest),'bytes':len(piece),'sha256':H(piece),'scope':'literal original source span'})
 source_records.append({'source':str(src),'snapshot':str(B/record['snapshot']),'bytes':len(data),'sha256':H(data),'scope':record.get('role','WHOLE inspected original source'),'cuts':cuts})
source_records.append({'source':str(P/'raw.log'),'snapshot':str(B/'final-integration/public-raw.log'),'bytes':len(public_raw),'sha256':H(public_raw),'scope':'Whole readback identity; ONLY ten complete own/local blocks reviewed, not the other 81 theorem blocks or two definitions','cuts':public_cuts})
for source,scope in [(P/'report.json','actual final readback receipt'),(P/'public.lean','actual public command source'),(A/'public-validation.json','root final public metadata'),(A/'source-validation.json','root final source/check metadata')]:
 dest=B/'final-integration'/(('public-'+source.name) if source.parent==P else source.name);data=dest.read_bytes()
 source_records.append({'source':str(source),'snapshot':str(dest),'bytes':len(data),'sha256':H(data),'scope':scope,'cuts':[]})
# The old Root local snapshot name is historical. Exact failed/successful sources are authoritative.
status={'status':'CLEAR / FINAL','measured_at':datetime.datetime.now().astimezone().isoformat(),'source_checkpoint':'ffe7569b0158d9dfeeb44b477b8c48841b626e10','own_modules':3,'own_public_theorems':8,'root_local_reviewed_public_theorems':2,'dependency_full_sources_reviewed':['SourcePruningEnumerationSharedTargetArity'],'public_full_blocks_reviewed':len(public_cuts),'public_bytes':len(public_raw),'public_sha256':H(public_raw),'source_validation':'Root validator PASS16modules+Audit; 79new/12unchanged public signatures','aggregate':'PASS4195jobs / 79883theorem dependencies; older replay unused inputs warning retained','strict_audit':'PASS56B expected axiom-count output','own_root_strict_status':['ClassEdit2 PASSraw0 after strict1 endpoint reduction failures','ClassPass1 PASSraw0 unchanged','Parent1 PASSraw0 unchanged','LocalReduction2 PASSraw0 after strict1 field-name correction'],'own_installed_builds':['ClassEdit1324','ClassPass1325','LocalReduction1498','Parent1982'],'remaining_global_gate':'Initial checked provenance and all-worker/history origin attachment are not derived from Packet by these observers.'}
(B/'final-status.json').write_text(json.dumps(status,indent=2)+'\n')
index={'status':'FINAL reviewed sources and exact literal spans','sources':source_records,'unreviewed':'Other new modules and public blocks are covered by Root/other workers, not this independent bounded semantic reading.'}
(B/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
report=(B/'review-source.txt').read_text().replace('SOURCE REVIEW CLEAR. Integration review remains OPEN until Root supplies final aggregate and public receipts.','CLEAR / FINAL. Root integration and installed public readback are complete.')
report+='''\nFinal integration: source checkpoint ffe7569b0158d9dfeeb44b477b8c48841b626e10. Full installed readback has 195567 bytes, SHA256 7119d146f5780ab89cb0d2bfcc3cdb8e894401cc41abf4b94c67e4f308b8771b. This review reads all ten complete public blocks for ClassEdit, ClassPass, Parent and Root LocalReduction. Each printed header retains its actual read/call and original cache/domain/range admissions, then initial Heap. Each axiom list is exactly propext, Classical.choice and Quot.sound. There is no sorryAx or hidden future Heap premise in those blocks. Shared internal node/children/rows/list observers explicitly take captured original availability; Class derives it from its existing original Values input.\n\nRoot's final validator records 91 full theorem signatures/axiom checks, 79 new and 12 unchanged, plus two printed declarations. This bounded review does not manually read the other 81 theorem blocks or two declarations, nor review new documentation. Aggregate Audit succeeds with 4195 jobs and 79883 checked theorem dependencies. Its old replay unused-input warning is retained. Strict Audit succeeds with the expected 56-byte axiom-count message. All relevant source identities and actual strict/build reports are copied and hashed. All five reviewed final files match installed repository bytes.\n\nStrongest new local claim: actual allocated class edits, their right fold, local reduction and checked Parent construction preserve projected arity of every native edge record from a genuine initial arity Heap. The exact live/reject/read endpoints remain the actual supplied endpoints. This gives a real worker preservation step toward same-bound origin decoration. It does not generate checked origins from Packet, decorate every ResourceHistory, or change the existing whole-enumeration acceptance/coverage claim. Generic Post keeps old records but is not used as a theorem that newly created records have arity.\n\nAll draft variants, the ClassEdit endpoint failures, Root's Local field-name failure/fix, actual successful checks/builds, original admissions, and the historical snapshot identity correction remain preserved. No repository changes, builds, Git operations, network calls or board actions were performed by this worker. No further writes follow the FROZEN seal.\n'''
(B/'report.txt').write_text(report)
# Verify each nested whole and literal span before sealing.
for record in source_records:
 data=Path(record['source']).read_bytes();assert len(data)==record['bytes'] and H(data)==record['sha256'];assert Path(record['snapshot']).read_bytes()==data
 for cut in record['cuts']:
  piece=b''.join(data.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']]);assert len(piece)==cut['bytes'] and H(piece)==cut['sha256'];assert Path(cut['snapshot']).read_bytes()==piece
payloads=[]
for p in sorted(B.rglob('*')):
 if p.is_file() and p.name not in {'FROZEN','pins.json'}:
  data=p.read_bytes();payloads.append({'path':str(p.relative_to(B)),'bytes':len(data),'sha256':H(data)})
(B/'pins.json').write_text(json.dumps({'payload_count':len(payloads),'payloads':payloads},indent=2)+'\n')
cutcount=sum(len(r['cuts']) for r in source_records);cutlines=sum(c['last_line']-c['first_line']+1 for r in source_records for c in r['cuts'])
seal={'status':'FINAL/FROZEN','scope':'Actual ClassEdit/ClassPass/Parent proofs and Root LocalReduction composition; ten installed public headers/axioms. No whole-system or documentation claim.','payload_count':len(payloads),'exact_file_count':len(payloads)+2,'pins_sha256':H((B/'pins.json').read_bytes()),'report_path':'report.txt','report_sha256':H((B/'report.txt').read_bytes()),'source_index_path':'source-index.json','source_index_sha256':H((B/'source-index.json').read_bytes()),'whole_count':len(source_records),'cut_count':cutcount,'cut_lines':cutlines,'root_checks':['strict-class-edit-arity-2','strict-class-pass-arity-1','strict-parent-arity-1','strict-local-reduction-arity-2','public-readback-final-1','strict-audit-1'],'no_further_writes':True,'sealed_at':datetime.datetime.now().astimezone().isoformat()}
(B/'FROZEN').write_text(json.dumps(seal,indent=2)+'\n')
print(json.dumps({**seal,'seal_sha256':H((B/'FROZEN').read_bytes())},indent=2))
