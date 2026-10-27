from pathlib import Path
import datetime,difflib,hashlib,json

area=Path('/tmp/mcfta-recursive-history-resources-20261027/history-boundary-isolation-draft')
root=Path('/home/tritlo/Code/mcfta')
hash_of=lambda data: hashlib.sha256(data).hexdigest()
write_json=lambda path,value: path.write_text(json.dumps(value,indent=2)+'\n')
checks=[('strict-boundary-history-1','SourcePruningEnumerationHistoryBoundaryIsolation.lean',1),
        ('strict-boundary-history-2','SourcePruningEnumerationHistoryBoundaryIsolation.lean',0),
        ('strict-finite-boundary-isolation-1','SourcePruningEnumerationFiniteBoundaryIsolation.lean',0),
        ('build-boundary-and-history-1',None,0)]
records=[]
for label,name,exit_code in checks:
    origin=area.parent/label
    files=['report.json','raw.log']+([f'MicroCFTA/{name}'] if name else [])
    copied=[]
    for relative in files:
        p=origin/relative;data=p.read_bytes();out=area/'evidence'/label/relative
        out.parent.mkdir(parents=True,exist_ok=True)
        assert not out.exists();out.write_bytes(data)
        copied.append({'original_path':str(p),'path':str(out.relative_to(area)),'bytes':len(data),'sha256':hash_of(data)})
    report=json.loads((origin/'report.json').read_text());raw=(origin/'raw.log').read_bytes()
    assert report['exit_code']==exit_code
    assert report['bytes']==len(raw) and report['sha256']==hash_of(raw)
    if name:
        data=(origin/'MicroCFTA'/name).read_bytes()
        assert report['source_sha256']==hash_of(data)
        if exit_code==0:
            assert raw==b''
            assert data==(root/'lean/MicroCFTA'/name).read_bytes()
    records.append({'label':label,'root_owned_check':True,'expected_exit_code':exit_code,
                    'report_raw_and_source_exact':True,'files':copied})
failed=(area/'evidence/strict-boundary-history-1/MicroCFTA/SourcePruningEnumerationHistoryBoundaryIsolation.lean').read_bytes()
final=(area/'evidence/strict-boundary-history-2/MicroCFTA/SourcePruningEnumerationHistoryBoundaryIsolation.lean').read_bytes()
original=(area/'drafts/SourcePruningEnumerationHistoryBoundaryIsolation.lean').read_bytes()
assert failed==original.replace(b'open EnumerationState EnumerationDischargeHistory InternedConstructorTemplates\n',
 b'open EnumerationState EnumerationDischargeHistory InternedConstructorTemplates EnumerationCorrectness\n')
assert final==failed.replace(b'else [.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata before), checked)]) =\n      [.ok ((updated, next), core)] at observed',
 b'else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata before), checked)]) =\n      [Except.ok ((updated, next), core)] at observed')
public_start=b'variable [DecidableEq Symbol]'
assert original.split(public_start,1)[1]==final.split(public_start,1)[1]
producer=(area/'drafts/SourcePruningEnumerationFiniteBoundaryIsolation.lean').read_bytes()
assert producer==(root/'lean/MicroCFTA/SourcePruningEnumerationFiniteBoundaryIsolation.lean').read_bytes()
for name,data in [('SourcePruningEnumerationHistoryBoundaryIsolation.lean',final),('SourcePruningEnumerationFiniteBoundaryIsolation.lean',producer)]:
    p=area/'final-sources'/name;p.parent.mkdir(exist_ok=True)
    assert not p.exists();p.write_bytes(data)
    lines=data.splitlines(keepends=True)
    if 'HistoryBoundary' in name:
        spans=[(26,42,'exact restart singleton fields, including the qualified constructors'),
               (56,124,'whole actual history induction and native endpoint preservation'),
               (126,136,'same-output non-discharge corollary')]
    else:
        spans=[(28,70,'entire original resource producer prefix and added original-marker output clause')]
    cut_rows=[]
    for first,last,purpose in spans:
        out=area/'final-cuts'/f'{Path(name).stem}-L{first}-L{last}.lean'
        out.parent.mkdir(exist_ok=True);cut=b''.join(lines[first-1:last]);assert not out.exists();out.write_bytes(cut)
        cut_rows.append({'path':str(out.relative_to(area)),'first_line':first,'last_line':last,'bytes':len(cut),'sha256':hash_of(cut),'purpose':purpose})
    write_json(area/f'final-{Path(name).stem}-source.json',{'source_path':str(root/'lean/MicroCFTA'/name),
        'copy':str(p.relative_to(area)),'bytes':len(data),'lines':len(lines),'sha256':hash_of(data),'cuts':cut_rows})
revisions=[]
for label,before,after in [('namespace-precheck',original,failed),('except-constructor-qualification',failed,final)]:
    patch_dir=area/'revisions'/label;patch_dir.mkdir(parents=True)
    forward=''.join(difflib.unified_diff(before.decode().splitlines(keepends=True),after.decode().splitlines(keepends=True),fromfile='before.lean',tofile='after.lean'))
    inverse=''.join(difflib.unified_diff(after.decode().splitlines(keepends=True),before.decode().splitlines(keepends=True),fromfile='after.lean',tofile='before.lean'))
    (patch_dir/'forward.patch').write_text(forward);(patch_dir/'inverse.patch').write_text(inverse)
    revisions.append({'label':label,'before_sha256':hash_of(before),'after_sha256':hash_of(after),
        'forward_patch':str((patch_dir/'forward.patch').relative_to(area)),'forward_sha256':hash_of(forward.encode()),
        'inverse_patch':str((patch_dir/'inverse.patch').relative_to(area)),'inverse_sha256':hash_of(inverse.encode())})
write_json(area/'root-revisions.json',{'original_saved_draft_sha256':hash_of(original),'final_installed_sha256':hash_of(final),
 'precheck_was_not_a_Lean_failure':True,'actual_failed_check':'strict-boundary-history-1',
 'only_reported_errors':'Two ambiguous .ok constructors in the private change expression, lines35 and36.',
 'all_public_theorem_text_and_proofs_byte_identical_after_namespace_open_and_private_helper':True,
 'producer_byte_exact_to_original_draft':True,'revisions':revisions})
write_json(area/'final-check-evidence.json',{'bound_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':records,
 'checks_were_run_by_root':True,'no_checks_or_repository_edits_by_this_agent':True})
print(json.dumps({'new_checks':len(records),'history_final_sha256':hash_of(final),'producer_final_sha256':hash_of(producer),
 'exact_delta':'one namespace open before first check; two constructor qualifications after the 901-byte failed check'}))
