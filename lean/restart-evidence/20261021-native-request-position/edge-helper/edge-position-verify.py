import argparse, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent

def checked(base,entry):
    data=(base/entry['path']).read_bytes()
    assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
    p.add_argument('--live',action='store_true')
    a=p.parse_args()
    m=json.loads((HERE/'edge-position-manifest.json').read_text())
    for e in m['files']: checked(HERE,e)
    for e in m['sources']:
        checked(HERE/'inputs/root',e)
        if a.live: checked(a.root,e)
    assert json.loads((HERE/'edge-position-source-pins.json').read_text())['files']==m['sources']
    s=json.loads((HERE/'edge-position-selection.json').read_text())
    assert s['finalized'] and s['lean_jobs']==4 and s['failed_checks']==2
    assert s['strict_jobs']==4 and s['warning_bearing_successes']==1
    assert s['public_jobs']==s['canonical_jobs']==s['new_public_pairs']==s['constructed_pairs']==0
    data=(HERE/s['source']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==s['source_sha256']
    assert data==(HERE/(s['selected_strict']+'.source.lean')).read_bytes()
    source=data.decode()
    snippet=(HERE/s['snippet']).read_text()
    assert hashlib.sha256(snippet.encode()).hexdigest()==s['snippet_sha256']
    assert snippet==source[source.index('private theorem edge_work_pos'):source.index('\nend MicroCFTA.SourceCurrentNativeRequestPositivePositions')]
    assert len(re.findall(r'^private theorem ',snippet,re.M))==5
    assert not re.search(r'^(?:theorem|def|inductive|structure) ',source,re.M)
    assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler',source)
    assert 'private theorem edge_body_pos [DecidableEq Symbol]' not in source
    for exact in ['SourceCurrentAllocatedNativePhysicalCompletion.Good before','SourceCurrentConstrainedCapCheckedJointEdge.body_effects','SourceEqualityIntersectionEdgeAllocation.run_correct','SourceCurrentUnconstrainedGuardClosure.loaded_ready_plain','SourceCurrentConstrainedCapNativeScope.edge_child','List.getElem?_zip_eq_some.mp selected','CodePos (source := source) code after.native.machine (fun _ result => EdgePos source request result)']:
        assert exact in snippet,exact
    for name,code in s['attempts'].items():
        meta=json.loads((HERE/(name+'.json')).read_text())
        assert meta['exit_code']==code
        assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
        assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=json.loads((HERE/(name+'.usage.json')).read_text())
        assert usage['age_seconds']<120 and usage['remaining_percent']>1
        assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
        assert '-Dlinter.all=true' in meta['command']
        assert meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
    assert not (HERE/(s['selected_strict']+'.log')).read_bytes()
    assert 'warning:' in (HERE/'edge-position-direct-3.log').read_text()
    assert all('error:' in (HERE/(f'edge-position-direct-{i}.log')).read_text() for i in [1,2])
    print(json.dumps({'status':'PASS','local_pins':len(m['files']),'root_pins':len(m['sources']),'lean_jobs':4,'failed_checks':2,'warning_bearing_unselected_successes':1,'new_public_pairs':0,'constructed_pairs':0,'canonical_jobs':0,'live':a.live}))
if __name__=='__main__': main()
