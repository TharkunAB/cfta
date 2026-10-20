import datetime, hashlib, json, re, shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
PREFIX='backedge-kernels'
STRICT='backedge-kernels-direct-5'
PUBLIC='backedge-kernels-public-1'
NAME='MicroCFTA.GeneratedRowCaptureBackedgeFixture.actual_generated_initial_capture_backedge'
def sha(data): return hashlib.sha256(data).hexdigest()
assert not (HERE/(PREFIX+'-manifest.json')).exists()
receipts={}
for p in HERE.glob(PREFIX+'-*.json'):
 if re.fullmatch(PREFIX+r'-(?:calculation|diagnostic|support|direct|public)-\d+',p.stem): receipts[p.stem]=json.loads(p.read_text())
assert receipts[STRICT]['exit_code']==0 and receipts[PUBLIC]['exit_code']==0
assert not (HERE/(STRICT+'.log')).read_bytes()
assert (HERE/(PREFIX+'.lean')).read_bytes()==(HERE/(STRICT+'.source.lean')).read_bytes()
ordered=sorted(receipts,key=lambda stem:receipts[stem]['started_at'])
selection=dict(finalized=True,source=PREFIX+'.lean',source_sha256=sha((HERE/(PREFIX+'.lean')).read_bytes()),
 public_heads=[NAME],selected_strict=STRICT,strict=STRICT,selected_public=PUBLIC,
 groups=[dict(name=PUBLIC,pairs=1,kind='constructed',full_proof=True)],
 printer_sha256=sha((HERE/(PREFIX+'-public.lean')).read_bytes()),public_log_bytes=(HERE/(PUBLIC+'.log')).stat().st_size,
 expected_exit_codes={s:receipts[s]['exit_code'] for s in ordered},lean_jobs=len(ordered),failed_attempts=sum(d['exit_code']!=0 for d in receipts.values()),
 production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,
 distinct_new_source_examples=1,attempted_source_variants=3,initial_capture_branch_forced=True,new_generated_target=True,
 leaves_occurrence=1,lexical_slot=2,encode_slot_claim=False)
(HERE/(PREFIX+'-selection.json')).write_text(json.dumps(selection,indent=2)+'\n')
shutil.copyfile(HERE/(PREFIX+'-peaks.txt'),HERE/(PREFIX+'-peaks-final.txt'))
report=HERE/(PREFIX+'-review.md')
report.write_text(report.read_text()+f"\nSelected evidence: {STRICT} has an empty raw log. {PUBLIC} prints the complete public type and proof with all eight options and standard axioms only. The component retains {len(ordered)} capped Lean attempts, including {selection['failed_attempts']} failed attempts. It owns zero production declarations and one constructed proof pair. It runs no canonical build. The independent normalized-prefix helper component is separate from these counts.\n")
files=[]
excluded={PREFIX+'-manifest.json',PREFIX+'-verification.json',PREFIX+'-live-verification.json',PREFIX+'-peaks.txt'}
for p in sorted(HERE.rglob('*')):
 if p.is_file():
  rel=str(p.relative_to(HERE))
  if rel in excluded: continue
  assert '__pycache__' not in p.parts
  data=p.read_bytes();files.append(dict(path=rel,bytes=len(data),sha256=sha(data)))
sources=json.loads((HERE/(PREFIX+'-source-pins.json')).read_text())['sources']
manifest=dict(schema=1,created_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=files,sources=sources)
(HERE/(PREFIX+'-manifest.json')).write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(manifest_sha256=sha((HERE/(PREFIX+'-manifest.json')).read_bytes()),file_pins=len(files),source_pins=len(sources),jobs=len(ordered),failed=selection['failed_attempts'],source=selection['source_sha256'])))
