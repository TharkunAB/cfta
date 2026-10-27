from pathlib import Path
import datetime,hashlib,json
area=Path('/tmp/mcfta-recursive-marker-attachment-20261027/marker-investigation')
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
sha=lambda d:hashlib.sha256(d).hexdigest()
specs=[
('SourcePruningEnumerationCreatedIsolation.lean',[(23,70,'actual clear creates isolation from genuine Ready and IncomingAvoid'),(104,160,'actual selected parking and opaque creation endpoints')]),
('SourcePruningEnumerationOpaqueSuffixIsolation.lean',[(23,30,'freshness derives suffix Avoids'),(65,84,'actual different-slot finalizer preserves isolation'),(118,187,'entire opaque suffix resource producer and same finalizer conclusion'),(217,234,'same actual suffix result and finalizer proof endpoint')]),
('SourcePruningEnumerationFiniteHistoryContract.lean',[(45,132,'ordinary receipt and exact parked/ordinary resource history tail endpoints')]),
('SourcePruningEnumerationHistoryBoundaryIsolation.lean',[(56,124,'checked original-marker tail persistence and actual native caller transport')]),
('SourcePruningEnumerationNativeContinuations.lean',[(40,70,'captured enum cache restored for siblings; Caller and queries threaded')]),
('SourcePruningEnumerationChildTraversal.lean',[(25,58,'actual child suffix thread and complete trace fields'),(70,119,'actual complete result derives exact per-child trace')]),
('SourcePruningEnumerationSelectedEdge.lean',[(69,82,'actual staged children and residual write')]),
('SourcePruningEnumerationCapturedEdge.lean',[(23,31,'same actual completed selected endpoint feeds captured finalizer')]),
('SourcePruningEnumerationIsolationReads.lean',[(77,92,'either callback side preserves isolation at actual returned core')]),
('SourcePruningEnumerationRecursion.lean',[(16,29,'actual native boundary and repeated-key clear')]),
('SourcePruningEnumerationSelectedStepCompletion.lean',[(308,329,'valid parked receipt supplies true check, attached core and actual Restart.run')]),
('EnumerationDriver.lean',[(218,227,'root read gives exact stored payload and explicit safety')]),
('SourcePruningEnumerationHeadAdmission.lean',[(70,104,'completed head hides local child creation points but keeps full Post and stable final result')]),
('SourcePruningEnumerationPrefixCompletion.lean',[(28,47,'actual PrefixValid invariant and full observation link')]),
('SourcePruningEnumerationRestart.lean',[(23,38,'raw singleton exact metadata, decision and core')]),
('EnumerationCompressionFrame.lean',[(76,88,'qualified actual getValue_frame declaration')]),
('SourcePruningEnumerationNodes.lean',[(49,75,'native Keeps retains actual decoded value across suffix Post')]),
]
rows=[]
for name,spans in specs:
 p=root/name;data=p.read_bytes();lines=data.splitlines(keepends=True)
 q=area/'sources'/name;q.parent.mkdir(exist_ok=True);assert not q.exists();q.write_bytes(data)
 row={'source_path':str(p),'copy':str(q.relative_to(area)),'bytes':len(data),'lines':len(lines),'sha256':sha(data),
      'review_scope':'focused literal cuts; whole copy is source provenance','cuts':[]}
 for first,last,purpose in spans:
  assert 1<=first<=last<=len(lines)
  d=b''.join(lines[first-1:last]);cut=area/'cuts'/f'{p.stem}-L{first}-L{last}.lean'
  cut.parent.mkdir(exist_ok=True);assert not cut.exists();cut.write_bytes(d)
  row['cuts'].append({'path':str(cut.relative_to(area)),'first_line':first,'last_line':last,'bytes':len(d),'sha256':sha(d),'purpose':purpose})
 rows.append(row)
index={'created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'full_copies':len(rows),
'cut_count':sum(len(r['cuts']) for r in rows),'cut_lines':sum(c['last_line']-c['first_line']+1 for r in rows for c in r['cuts']),
'policy':'TEMP-only; no prior bundle edits, repository edits, compiler/build, Git, network or board operations', 'sources':rows}
(area/'source-pins.json').write_text(json.dumps(index,indent=2)+'\n')
origin=area.parent/'strict-parked-attachment-1';records=[]
for relative in ['report.json','raw.log','MicroCFTA/SourcePruningEnumerationParkedMarkerAttachment.lean']:
 p=origin/relative;data=p.read_bytes();q=area/'evidence/strict-parked-attachment-1'/relative
 q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();q.write_bytes(data)
 records.append({'source_path':str(p),'copy':str(q.relative_to(area)),'bytes':len(data),'sha256':sha(data)})
r=json.loads((origin/'report.json').read_text());raw=(origin/'raw.log').read_bytes()
assert r['exit_code']==1 and r['bytes']==len(raw)==4888 and r['sha256']==sha(raw)
assert r['source_sha256']==sha((area/'drafts/SourcePruningEnumerationParkedMarkerAttachment.lean').read_bytes())
(area/'failed-check.json').write_text(json.dumps({'check_owned_by_root':True,'raw_report_source_exact':True,'files':records},indent=2)+'\n')
print({k:index[k] for k in ['full_copies','cut_count','cut_lines']})
