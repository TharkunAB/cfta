exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import datetime,difflib,re,shutil
metadata=HERE/'root-metadata-history'
metadata.mkdir()
metadata_jobs={}
for path in sorted(Path('/tmp').glob('mcfta-fresh-node-counter-growth-*.json')):
    item=load(path)
    if not isinstance(item,dict) or 'wrapper' not in item or 'exit_code' not in item:
        continue
    assert Path(item['command'][0]).name not in {'lean','lake'}
    for suffix in ['.json','.log','.limits.json','.usage.json','.source.py','.peaks.txt']:
        original=path.with_name(path.stem+suffix)
        assert original.is_file(),original
        shutil.copy2(original,metadata/original.name)
        assert sha(original)==sha(metadata/original.name)
    metadata_jobs['root-metadata-history/'+path.name]=item['exit_code']
failures=[path for path,code in metadata_jobs.items() if code!=0]
assert failures==['root-metadata-history/mcfta-fresh-node-counter-growth-strict-selection-1.json']
save('root-metadata-history-cut.json',dict(status='COMPLETE_TERMINAL_METADATA_CUT_BEFORE_CLOSING_TOOLS',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),jobs=metadata_jobs,failed_jobs=len(failures),
    later_receipts='The one-time completed-root-support collection retains all closing receipts after this cut.'))
specs={'strict1':('strict',NAME),'strict2':('strict',NAME),'strict3':('strict',NAME),'FULL1':('full',NAME),'audit1':('audit',None)}
actual={}
for path in HERE.glob('*.json'):
    item=load(path)
    if isinstance(item,dict) and 'wrapper' in item and 'exit_code' in item and Path(item['command'][0]).name in {'lean','lake'}:
        actual[path.stem]=item
assert set(actual)==set(specs)
jobs={}
for stem,(kind,module) in specs.items():
    receipt=actual[stem]
    raw=(HERE/receipt['log']).read_text()
    jobs[stem]=dict(kind=kind,module=module,exit_code=receipt['exit_code'],source_sha256=receipt.get('sha256'),
        log_sha256=sha(HERE/receipt['log']),
        errors=len(re.findall(r'^.+?:\d+:\d+: error(?:\([^)]*\))?:',raw,re.M)),
        source_warnings=len(re.findall(r'^.+?:\d+:\d+: warning(?:\([^)]*\))?:',raw,re.M)))
    assert load(HERE/receipt['limits'])=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
    usage=load(HERE/(stem+'.usage.json'))
    assert 0<=usage['age_seconds']<=600 and usage['remaining_percent']>1
assert (jobs['strict1']['exit_code'],jobs['strict1']['errors'],jobs['strict1']['source_warnings'])==(1,6,2)
assert (jobs['strict2']['exit_code'],jobs['strict2']['errors'],jobs['strict2']['source_warnings'])==(0,0,1)
assert (HERE/'strict3.log').read_bytes()==b''
assert all(jobs[stem]['exit_code']==0 for stem in ['strict3','FULL1','audit1'])
save('job-history.json',jobs)
reasons={
    'v1':'Initial uncompiled body. V2 corrects one scoped continuation binder name before any compiler run.',
    'v2':'First actual strict source. The six elaboration errors and two unused-instance warnings are retained.',
    'v3':'Explicit actual-state and base-equation repairs. Strict2 typechecks with one retained omit warning.',
    'v4':'Explicit theorem instances remove the global instance and omit. All six proof bodies remain unchanged; strict3 and sole FULL1 are clean.'}
variants=[]
for version,reason in reasons.items():
    path='variants/'+version+'/'+NAME+'.lean'
    source=HERE/path
    lines=len(source.read_bytes().splitlines())
    assert 0<lines<=180
    variants.append(dict(module=NAME,path=path,sha256=sha(source),lines=lines,reason=reason))
assert sha(HERE/variants[-1]['path'])==sha(HERE/(NAME+'.lean'))==load(HERE/'selected-source-gate.json')['source_sha256']
patches=[]
for before,after,reason in [('v1','v2','Match the exact reviewed scoped continuation binder name.'),
                           ('v2','v3','Repair actual state inference and base equations; retain the intermediate omit declaration.'),
                           ('v3','v4','Use explicit theorem instances; retain all six mathematical proof bodies unchanged.')]:
    old='variants/'+before+'/'+NAME+'.lean'
    new='variants/'+after+'/'+NAME+'.lean'
    path='patches/'+before+'-to-'+after+'.patch'
    expected=''.join(difflib.unified_diff((HERE/old).read_text().splitlines(keepends=True),
        (HERE/new).read_text().splitlines(keepends=True),fromfile=old,tofile=new))
    assert (HERE/path).read_text()==expected
    patches.append(dict(module=NAME,before=old,after=new,path=path,sha256=sha(HERE/path),reason=reason))
excluded={'source-history-gate.json','archived-components.json','current-progress.md'}|{row['path'] for row in variants}
artifacts=[]
for path in sorted(HERE.rglob('*')):
    if path.is_file() and str(path.relative_to(HERE)) not in excluded:
        artifacts.append(dict(path=str(path.relative_to(HERE)),bytes=path.stat().st_size,sha256=sha(path)))
assert not {row['path'] for row in variants}&{row['path'] for row in artifacts}
selection=load(HERE/'selected-sources.json')
save('source-history-gate.json',dict(status='ROOT_ACCEPTED',selected_sources={p:r['sha256'] for p,r in selection.items()},
    variants=variants,artifacts=artifacts,patches=patches,rejected_public_types=[]))
raw=(HERE/'audit1.log').read_text()
build=re.search(r'Build completed successfully \((\d+) jobs\)\.',raw)
dependencies=re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',raw)
assert build and dependencies and (int(build.group(1)),int(dependencies.group(1)))==(3652,75541)
assert sha(HERE/'audit1.log')=='f5d1bbe1ff0b0e8bafc4c54678f17c0bc1ab259d7541b86d273353a6ef735bb3'
warnings=re.findall(r'(?m)^warning: .+$',raw)
assert len(warnings)==1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in warnings[0]
metrics=dict(actual_jobs=len(jobs),source_jobs=sum(j['kind'] in {'strict','full'} for j in jobs.values()),
    focused_build_jobs=sum(j['kind']=='focused_build' for j in jobs.values()),audit_jobs=sum(j['kind']=='audit' for j in jobs.values()),
    failed_jobs=sum(j['exit_code']!=0 for j in jobs.values()),
    warned_source_exit_zero_jobs=sum(j['kind'] in {'strict','full'} and j['exit_code']==0 and j['source_warnings']>0 for j in jobs.values()),
    rejected_public_type_jobs=0)
save('actual-proof-cut.json',dict(status='ACTUAL_AUDIT_AND_HISTORY_BOUND',metrics=metrics,
    audit=dict(stem='audit1',build_jobs=int(build.group(1)),dependencies=int(dependencies.group(1)),log_sha256=sha(HERE/'audit1.log'),warnings=warnings),
    metadata_jobs=len(metadata_jobs),failed_metadata_jobs=len(failures),metadata_failure_paths=failures,
    variants=len(variants),patches=len(patches),artifacts=len(artifacts),source_history_sha256=sha(HERE/'source-history-gate.json'),
    original_Audit_sha256=sha(HERE/'original-sources/Audit.original.lean.txt')))
print(json.dumps(load(HERE/'actual-proof-cut.json')))
