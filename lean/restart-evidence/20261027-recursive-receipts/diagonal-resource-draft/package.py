from pathlib import Path
import json,hashlib,datetime,re
repo=Path('/home/tritlo/Code/mcfta')
out=Path('/tmp/mcfta-recursive-receipts-20261027/diagonal-resource-draft')
sha=lambda b:hashlib.sha256(b).hexdigest()
def write(p,b):
 p=out/p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(p,x):write(p,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
sources=[];cuts=[]
items=[
('SourcePruningEnumerationCapturedEdgeDiagonalSoundness',[(35,86),(111,147)],'whole existing diagonal bridge and corollary read'),
('SourcePruningEnumerationCapturedEdgeResources',[(193,256)],'whole existing resource producer and projection read'),
('SourcePruningEnumerationCapturedEdgeResourceSoundness',[(36,91),(125,176)],'whole existing stable resource soundness source read'),
('SourcePruningEnumerationCapturedEdgeCanonical',[(34,82)],'whole existing captured Canonical observer read; not called by draft'),
('SourcePruningEnumerationSelectedEdgeNeutralResourceSoundness',[(35,92)],'whole existing selected neutral resource soundness source read'),
('SourcePruningEnumerationCapturedEdge',[(23,31),(46,93)],'actual runtime and original completion admission read; historical proof suffix preserved but not freshly audited')]
for name,parts,scope in items:
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();dest='inputs/lean/MicroCFTA/'+name+'.lean';write(dest,b)
 sources.append({'path':str(p),'source':str(p),'snapshot':dest,'bytes':len(b),'sha256':sha(b),'read_scope':scope})
 lines=b.splitlines(keepends=True)
 for start,end in parts:
  assert 1<=start<=end<=len(lines),(name,start,end,len(lines))
  raw=b''.join(lines[start-1:end]);dest=f'cuts/{name}--{start}-{end}.lean';write(dest,raw)
  cuts.append({'path':str(p),'source':str(p),'snapshot':dest,'start':start,'end':end,'source_sha256':sha(b),'bytes':len(raw),'sha256':sha(raw)})
draft=out/'SourcePruningEnumerationCapturedEdgeDiagonalResourceSoundness.lean';b=draft.read_bytes();assert len(b)==10535 and sha(b)=='6a61e347e9d923f4c2d4c0178e766be335c6af851561d54978bd70feb3c7cea6'
assert b==(out/'revisions/001-initial.lean').read_bytes();text=b.decode()
assert len(text.splitlines())==151
assert text.count('\n    complete_resources seed formulas solver')==1
assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|Ranges)\b',text)
norm=lambda s:re.sub(r'\s+',' ',s).strip()
sound=(repo/'lean/MicroCFTA/SourcePruningEnumerationCapturedEdgeResourceSoundness.lean').read_text()
producer=(repo/'lean/MicroCFTA/SourcePruningEnumerationCapturedEdgeResources.lean').read_text()
resource_admission=sound[sound.index('    (seed :'):sound.index('    (canonical :')]
bridge=text[text.index('    (seed :'):text.index('    {bound :')]
assert bridge==resource_admission
start=producer.index('    (seed :',producer.index('theorem complete_resources'))
old_admission=producer[start:producer.index(' :\n    ∃',start)]
old_admission=old_admission.replace('(seed : Seed)','(seed : SourcePruningEnumerationIncomingReservation.Seed)').replace('(fits : Fits ','(fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits ').replace('(reserved : Reserved ','(reserved : SourcePruningEnumerationIncomingReservation.Reserved ').replace('(known : Heap ','(known : SourceEqualityAnnotationHeap.Heap ')
assert norm(bridge)==norm(old_admission)
cor=text[text.index('theorem diagonal_complete_sound_current_resources'):]
cor_admission=cor[cor.index('    (seed :'):cor.index('    (canonical :')]
assert cor_admission==resource_admission
sound_gates=sound[sound.index('    (canonical :'):sound.index('    {r n p h k :')]
cor_gates=cor[cor.index('    (canonical :'):cor.index('    {bound :')]
assert sound_gates==cor_gates
sound_conclusion=sound[sound.index('    ∀ (ambient :'):sound.index(' := by',sound.index('    ∀ (ambient :'))]
cor_conclusion=cor[cor.index('    ∀ (ambient :'):cor.index(' := by',cor.index('    ∀ (ambient :'))]
assert sound_conclusion==cor_conclusion
for key,raw in [('producer-admission-normalized.txt',norm(old_admission)),('bridge-admission-normalized.txt',norm(bridge)),('stable-semantic-gates.txt',sound_gates),('diagonal-semantic-gates.txt',cor_gates),('stable-backward-conclusion.txt',sound_conclusion),('diagonal-backward-conclusion.txt',cor_conclusion)]:write('contracts/'+key,(raw+'\n').encode())
js('contracts/comparison.json',{'status':'PASS source-text comparisons only; no compiler','bridge_admission_equals_original_resource_producer':True,'corollary_admission_equals_existing_stable_resource_soundness':True,'semantic_gates_byte_identical':True,'backward_conclusion_byte_identical':True,'resource_producer_calls_in_bridge':1,'diagonal_family':'bound+extra on representative/native/P/H/index','common_bound':'bound+r+n+p+h+k','identified_result':'same complete fragment/full Caller/saved Queries/Cached','no_full_memos_equality_inferred':True,'new_future_ranges_or_success_admission':False})
js('source-pins.json',{'version':1,'status':'FINAL SOURCE REVIEW CLEAR — UNBUILT PROOF DRAFT','observed_at':datetime.datetime.now().astimezone().isoformat(),'sources':sources,'cuts':cuts,'draft':{'path':str(draft),'bytes':len(b),'lines':151,'sha256':sha(b),'revision':'revisions/001-initial.lean','public_theorems':['stable_complete_of_diagonal_resources','diagonal_complete_sound_current_resources']},'compiler_evidence':False,'limits':'Original resource/current semantic gates and actual stable diagonal completion remain explicit; no low-fuel uniqueness, future Ranges or whole recursive acceptance.'})
for s in sources:assert (out/s['snapshot']).read_bytes()==Path(s['source']).read_bytes()
for c in cuts:assert (out/c['snapshot']).read_bytes()==b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']])
files=[p for p in sorted(out.rglob('*'))if p.is_file()and p not in {out/'pins.json',out/'FROZEN.json'}]
js('pins.json',{'version':1,'pins':[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in files]});raw=(out/'pins.json').read_bytes()
f={'status':'FROZEN SOURCE-REVIEWED UNBUILT PROOF DRAFT','pins_count':len(files),'pins_bytes':len(raw),'pins_sha256':sha(raw),'source_count':len(sources),'source_whole_snapshots':len(sources),'cut_count':len(cuts),'cut_lines':sum(c['end']-c['start']+1 for c in cuts),'draft_lines':151,'draft_sha256':sha(b),'report_sha256':sha((out/'report.txt').read_bytes()),'source_pins_sha256':sha((out/'source-pins.json').read_bytes()),'compiler_evidence':False};js('FROZEN.json',f)
for item in json.loads(raw)['pins']:
 data=(out/item['path']).read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256']
assert len(files)+2==sum(p.is_file()for p in out.rglob('*'))
print(json.dumps(f,indent=2));print('FROZEN SHA256',sha((out/'FROZEN.json').read_bytes()));print('Exact files',len(files)+2)
