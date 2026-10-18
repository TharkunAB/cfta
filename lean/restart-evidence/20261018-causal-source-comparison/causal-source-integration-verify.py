import hashlib
import importlib.util
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'causal-source-integration-manifest.json').read_text())
    for e in m['entries']:
        p=ROOT/e['path']; assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],p
    s=json.loads((HERE/'causal-source-integration-selection.json').read_text())
    assert s['finalized'] and s['owned_lean_runs']==6
    assert [s[k] for k in ['public_pairs','constructed_pairs','auxiliary_pairs']]==[0,1,0]
    assert sha(HERE/s['source'])==s['sha256']
    selected=json.loads((HERE/(s['strict']+'.json')).read_text())
    assert selected['sha256']==s['sha256']
    assert not (HERE/(s['strict']+'.log')).read_bytes()
    stems=[s['strict'],s['groups'][0]['name']]+[x['stem'] for x in s['retained_unselected']]
    for stem in stems:
        meta=json.loads((HERE/(stem+'.json')).read_text())
        expected=1 if stem in ['causal-source-integration-direct-1','causal-source-integration-direct-2'] else 0
        assert meta['exit_code']==expected
        assert sha(HERE/meta['source'])==meta['sha256']
        assert meta['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
    spec=importlib.util.spec_from_file_location('probes',HERE/'causal-source-integration-probe-check.py')
    probes=importlib.util.module_from_spec(spec);spec.loader.exec_module(probes)
    for g in s['groups']: probes.check_group(g)
    source=(HERE/s['source']).read_text()
    private=source.split('private theorem checked ',1)[1].split(' := by\n',1)[0]
    public=source.split('theorem actual_nested_pair ',1)[1].split(' := checked smart used warm',1)[0]
    assert private==public
    probe=json.loads((HERE/(s['groups'][0]['name']+'.json')).read_text())
    assert (HERE/probe['source']).read_text().startswith(source)
    assert source.count('\ntheorem ')==1
    assert 'SourceCurrentCausalHistoryProfiles.compare' in source
    assert 'SourceCurrentCausalSourceComparison.build_heap' in source
    assert 'firstAssignment (.uninterned 10) = secondAssignment (.uninterned 20)' in public
    assert 'reader.nodes.next = coldRight.nodes.next + 1' in public
    assert m['groups']==s['groups']
    print(json.dumps({'status':'PASS','entries':len(m['entries']),'public_pairs':0,'constructed_pairs':1,'auxiliary_pairs':0,'owned_lean_runs':6},sort_keys=True))
if __name__=='__main__':main()
