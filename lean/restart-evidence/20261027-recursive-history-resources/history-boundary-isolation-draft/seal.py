from pathlib import Path
import datetime,difflib,hashlib,json,re

area=Path('/tmp/mcfta-recursive-history-resources-20261027/history-boundary-isolation-draft')
hash_of=lambda d:hashlib.sha256(d).hexdigest()
assert not (area/'FROZEN').exists() and not (area/'pins.json').exists()
index=json.loads((area/'index.json').read_text())
for row in index['sources']:
    data=(area/row['copy']).read_bytes()
    assert len(data)==row['bytes'] and hash_of(data)==row['sha256']
    assert Path(row['source_path']).read_bytes()==data
    lines=data.splitlines(keepends=True)
    assert len(lines)==row['lines']
    for cut in row['cuts']:
        d=(area/cut['path']).read_bytes()
        assert len(d)==cut['bytes'] and hash_of(d)==cut['sha256']
        assert d==b''.join(lines[cut['first_line']-1:cut['last_line']])
checks=[]
for label in ['supporting-history-receipt-isolation-2','supporting-finite-history-resources-1',
              'strict-boundary-history-1','strict-boundary-history-2','strict-finite-boundary-isolation-1','build-boundary-and-history-1']:
    folder=area/'evidence'/label;report=json.loads((folder/'report.json').read_text());raw=(folder/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and hash_of(raw)==report['sha256']
    if label=='strict-boundary-history-1':
        assert report['exit_code']==1 and len(raw)==901 and raw.count(b'error(lean.invalidDottedIdent)')==2
    else:
        assert report['exit_code']==0
        if label!='build-boundary-and-history-1': assert raw==b''
    sources=list(folder.rglob('*.lean'))
    if 'source_sha256' in report:
        assert len(sources)==1 and hash_of(sources[0].read_bytes())==report['source_sha256']
    limits=report['cgroup_limits']
    assert limits['memory.max']=='4294967296' and limits['memory.high']=='4294967296' and limits['memory.swap.max']=='0'
    checks.append({'label':label,'exit_code':report['exit_code'],'raw_bytes':len(raw),'raw_sha256':hash_of(raw),'source_sha256':report.get('source_sha256')})
legacy=json.loads((area/'handoff-pins.json').read_text())
for relative,row in legacy['files'].items():
    data=(area/relative).read_bytes()
    assert len(data)==row['bytes'] and hash_of(data)==row['sha256']
original=(area/'drafts/SourcePruningEnumerationHistoryBoundaryIsolation.lean').read_bytes()
failed=(area/'evidence/strict-boundary-history-1/MicroCFTA/SourcePruningEnumerationHistoryBoundaryIsolation.lean').read_bytes()
final=(area/'final-sources/SourcePruningEnumerationHistoryBoundaryIsolation.lean').read_bytes()
versions={'namespace-precheck':(original,failed),'except-constructor-qualification':(failed,final)}
revisions=json.loads((area/'root-revisions.json').read_text())
for row in revisions['revisions']:
    before,after=versions[row['label']]
    assert hash_of(before)==row['before_sha256'] and hash_of(after)==row['after_sha256']
    forward=''.join(difflib.unified_diff(before.decode().splitlines(keepends=True),after.decode().splitlines(keepends=True),fromfile='before.lean',tofile='after.lean')).encode()
    inverse=''.join(difflib.unified_diff(after.decode().splitlines(keepends=True),before.decode().splitlines(keepends=True),fromfile='after.lean',tofile='before.lean')).encode()
    assert (area/row['forward_patch']).read_bytes()==forward and hash_of(forward)==row['forward_sha256']
    assert (area/row['inverse_patch']).read_bytes()==inverse and hash_of(inverse)==row['inverse_sha256']
assert hash_of(original)=='93520c507017be7968222831158b384a4b87afd490e64baba1f2a2f228bc88bb'
assert hash_of(final)=='73428a574a04a91c4b6d34b4bbd5a43414df252eda154b8b0183d7324bee0090'
producer=(area/'final-sources/SourcePruningEnumerationFiniteBoundaryIsolation.lean').read_bytes()
assert producer==(area/'drafts/SourcePruningEnumerationFiniteBoundaryIsolation.lean').read_bytes()
assert hash_of(producer)=='8c62789f246bacc34d19265ae5d7441b37712c798b0b25a50277da149943ef6e'
old=(area/'sources/SourcePruningEnumerationFiniteHistoryResources.lean').read_text()
new=producer.decode();norm=lambda s:re.sub(r'\s+','',s)
old_head=old.split('theorem run_finite_complete_resources_with_history',1)[1].split(' :\n    ∃ bound outcome,',1)[0]
new_head=new.split('theorem run_finite_complete_resources_isolated',1)[1].split('    (held heldHandle : Nat)',1)[0].rstrip()
assert norm(old_head)==norm(new_head)
old_result=old.split('    ∃ bound outcome,',1)[1].split(' :=\n',1)[0]
new_result=new.split('    ∃ bound outcome,',1)[1].split(' ∧\n      ∀ output ∈',1)[0]
new_result=new_result.replace('      (∀ extra output,','      ∀ extra output,',1)[:-1]
assert norm(old_result)==norm(new_result)
validation={'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'CLEAR',
 'all_primary_live_wholes_and_literal_slices_exact':True,'legacy_handoff_payloads_preserved_exact':True,
 'original_and_final_sources_exact':True,'all_root_reports_raws_and_snapshots_exact':True,
 'revisions_and_bidirectional_patches_exact':True,'entire_old_input_and_result_prefix_retained':True,
 'checks':checks,'no_compiler_or_repository_edits_by_this_agent':True}
(area/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
files=[p for p in sorted(area.rglob('*')) if p.is_file()]
assert not any(p.is_symlink() for p in area.rglob('*'))
payloads={str(p.relative_to(area)):{'bytes':p.stat().st_size,'sha256':hash_of(p.read_bytes())} for p in files}
pins={'algorithm':'sha256','payload_count':len(payloads),'files':payloads}
(area/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
frozen={'status':'FINAL/FROZEN/CLEAR','sealed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'pins_sha256':hash_of((area/'pins.json').read_bytes()),
 'report_sha256':hash_of((area/'report.txt').read_bytes()),'index_sha256':hash_of((area/'index.json').read_bytes()),
 'final_history_source_sha256':hash_of(final),'final_producer_source_sha256':hash_of(producer),
 'checks':'Root-owned strict history2 and finite-boundary1 PASS0/raw0; all failed/initial sources retained.',
 'scope':'Same original marker; actual decision and own output cache/caller. No creation-to-history attachment claim.',
 'no_further_writes':True}
(area/'FROZEN').write_text(json.dumps(frozen,indent=2)+'\n')
actual={str(p.relative_to(area)) for p in area.rglob('*') if p.is_file()}
assert actual==set(payloads)|{'pins.json','FROZEN'}
for relative,row in payloads.items():
    data=(area/relative).read_bytes();assert len(data)==row['bytes'] and hash_of(data)==row['sha256']
print(json.dumps({'payloads':len(payloads),'files':len(actual),'FROZEN_sha256':hash_of((area/'FROZEN').read_bytes()),
 'pins_sha256':frozen['pins_sha256'],'report_sha256':frozen['report_sha256'],'index_sha256':frozen['index_sha256']}))
