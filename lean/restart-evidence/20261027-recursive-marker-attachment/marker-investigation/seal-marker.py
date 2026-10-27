from pathlib import Path
import datetime,hashlib,json
area=Path('/tmp/mcfta-recursive-marker-attachment-20261027/marker-investigation');sha=lambda b:hashlib.sha256(b).hexdigest()
assert not(area/'FROZEN').exists() and not(area/'pins.json').exists()
sources=json.loads((area/'source-pins.json').read_text())['sources']+json.loads((area/'checked-source-pins.json').read_text())['sources']
for r in sources:
 d=(area/r['copy']).read_bytes();assert Path(r['source_path']).read_bytes()==d and sha(d)==r['sha256'] and len(d)==r['bytes']
 for c in r['cuts']:
  b=(area/c['path']).read_bytes();assert b==b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]) and sha(b)==c['sha256']
versions=['drafts/SourcePruningEnumerationParkedMarkerAttachment.lean','revisions/v2/SourcePruningEnumerationParkedMarkerAttachment.lean','revisions/v3/SourcePruningEnumerationParkedMarkerAttachment.lean']
checks=[]
for i,rel in enumerate(versions,1):
 folder=area/'evidence'/f'strict-parked-attachment-{i}';r=json.loads((folder/'report.json').read_text());raw=(folder/'raw.log').read_bytes();d=(area/rel).read_bytes()
 assert (folder/'MicroCFTA/SourcePruningEnumerationParkedMarkerAttachment.lean').read_bytes()==d
 assert r['source_sha256']==sha(d) and r['bytes']==len(raw) and r['sha256']==sha(raw)
 assert r['exit_code']==(0 if i==3 else 1) and len(raw)==[4888,48802,0][i-1]
 checks.append({'label':folder.name,'source_sha256':sha(d),'exit_code':r['exit_code'],'raw_bytes':len(raw)})
for name in ['handoff-pins.json','handoff-v3-pins.json','handoff-checked-v3-pins.json']:
 for rel,r in json.loads((area/name).read_text())['files'].items():
  d=(area/rel).read_bytes();assert sha(d)==r['sha256'] and len(d)==r['bytes']
headers=[(area/p).read_text().split('theorem parked_tail_created_isolated',1)[1].split(' := by',1)[0] for p in versions]
assert headers[0]==headers[1]==headers[2]
index={'status':'FINAL CLEAR','source_checkpoint_reported_by_root':'d60f6c1607d39fa114ae83a489af7b34d832ad23',
'sources':sources,'whole_copies':len(sources),'cut_count':sum(len(r['cuts']) for r in sources),'cut_lines':sum(c['last_line']-c['first_line']+1 for r in sources for c in r['cuts']),
'final_report':'report-final.txt','all_attempts':checks,'older_OPEN_records':'Retained historical handoffs; superseded by final report and FROZEN.'}
(area/'index.json').write_text(json.dumps(index,indent=2)+'\n')
(area/'validation-final.json').write_text(json.dumps({'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all_live_wholes_and_literal_cuts_exact':True,'all_three_attempts_exact':True,'all_prior_handoff_payloads_exact':True,'public_statement_unchanged':True,'checks_run_by_root_only':True,'reviewer_repository_and_build_mutations':0},indent=2)+'\n')
paths=sorted(p for p in area.rglob('*') if p.is_file());payloads=[{'path':str(p.relative_to(area)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in paths]
(area/'pins.json').write_text(json.dumps({'algorithm':'sha256','payload_count':len(payloads),'payloads':payloads},indent=2)+'\n')
frozen={'status':'FINAL/FROZEN/CLEAR','sealed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'pins_sha256':sha((area/'pins.json').read_bytes()),'report_path':'report-final.txt','report_sha256':sha((area/'report-final.txt').read_bytes()),'index_sha256':sha((area/'index.json').read_bytes()),'final_source_sha256':checks[2]['source_sha256'],'no_further_writes':True}
(area/'FROZEN').write_text(json.dumps(frozen,indent=2)+'\n')
assert {str(p.relative_to(area)) for p in area.rglob('*') if p.is_file()}=={r['path'] for r in payloads}|{'pins.json','FROZEN'}
for r in payloads:assert sha((area/r['path']).read_bytes())==r['sha256']
print(json.dumps({'payloads':len(payloads),'files':len(payloads)+2,'FROZEN_sha256':sha((area/'FROZEN').read_bytes()),'pins_sha256':frozen['pins_sha256'],'report_sha256':frozen['report_sha256'],'whole_sources':len(sources),'cuts':index['cut_count'],'cut_lines':index['cut_lines']}))
