exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import difflib
old_history=HERE/'source-history-gate.json'
old_cut=HERE/'actual-proof-cut.json'
assert sha(old_history)=='266b703fc0149d067a1044e961a67bcf04a3e1465465283f92175c5ba86851e5'
history=load(old_history)
cut=load(old_cut)
assert len(history['variants'])==4 and len(history['patches'])==3 and cut['artifacts']==2281
for patch in history['patches']:
    assert 'fromfile' not in patch and 'tofile' not in patch
    patch.update(fromfile=patch['before'],tofile=patch['after'])
    expected=''.join(difflib.unified_diff((HERE/patch['before']).read_text().splitlines(keepends=True),
        (HERE/patch['after']).read_text().splitlines(keepends=True),fromfile=patch['fromfile'],tofile=patch['tofile']))
    assert (HERE/patch['path']).read_text()==expected
drafts=HERE/'history-drafts/v1'
drafts.mkdir(parents=True,exist_ok=False)
for original in [old_history,old_cut]:
    (drafts/original.name).write_bytes(original.read_bytes())
before_artifacts={row['path']:row for row in history['artifacts']}
excluded={'source-history-gate.json','actual-proof-cut.json','archived-components.json','current-progress.md'}|{row['path'] for row in history['variants']}
artifacts=[]
for path in sorted(HERE.rglob('*')):
    relative=str(path.relative_to(HERE))
    if path.is_file() and relative not in excluded:
        artifacts.append(dict(path=relative,bytes=path.stat().st_size,sha256=sha(path)))
after_artifacts={row['path']:row for row in artifacts}
assert all(after_artifacts[path]==pin for path,pin in before_artifacts.items())
assert set(after_artifacts)-set(before_artifacts)=={'history-drafts/v1/source-history-gate.json','history-drafts/v1/actual-proof-cut.json'}
history['artifacts']=artifacts
old_history.write_text(json.dumps(history,indent=2)+'\n')
cut.update(artifacts=len(artifacts),source_history_sha256=sha(old_history),
    source_history_schema_revision=dict(previous_history_sha256=sha(drafts/'source-history-gate.json'),
        preserved_previous_cut='history-drafts/v1/actual-proof-cut.json',
        repair='Add exact retained unified-diff fromfile and tofile labels to all three patch records.',
        proof_jobs_changed=False,metadata_cut_changed=False,verifier_guard_changed=False))
old_cut.write_text(json.dumps(cut,indent=2)+'\n')
print(json.dumps(cut))
