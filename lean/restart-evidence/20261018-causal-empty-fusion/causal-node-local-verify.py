import hashlib
import importlib.util
import json
import re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'causal-node-local-manifest.json').read_text())
    for e in m['entries']:
        p=ROOT/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],p
    s=json.loads((HERE/'causal-node-local-selection.json').read_text())
    assert s['finalized'] and s['owned_lean_runs']==6
    assert [s[k] for k in ['public_pairs','constructed_pairs','auxiliary_pairs']]==[1,1,0]
    assert sha(ROOT/s['production'])==s['sha256']
    assert json.loads((HERE/(s['strict']+'.json')).read_text())['sha256']==s['sha256']
    stems=[s['strict'],s['canonical'],s['constructed_strict']]+[g['name'] for g in s['groups']]+[a['stem'] for a in s['retained_unselected']]
    for stem in stems:
        meta=json.loads((HERE/(stem+'.json')).read_text())
        assert meta['exit_code']==(1 if stem=='causal-node-local-kernels-1' else 0)
        assert meta['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        if 'source' in meta:assert sha(HERE/meta['source'])==meta['sha256']
    for stem in [s['strict'],s['constructed_strict']]:assert not (HERE/(stem+'.log')).read_bytes()
    canonical=(HERE/(s['canonical']+'.log')).read_text()
    assert 'Build completed successfully' in canonical and not re.search(r'warning:|error:',canonical)
    spec=importlib.util.spec_from_file_location('probes',HERE/'causal-node-local-probe-check.py')
    p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
    for g in s['groups']:p.check_group(g)
    source=(ROOT/s['production']).read_text()
    assert source.count('\ntheorem ')==1
    assert 'SourceCurrentCausalGeneratedEmpty.generated reader history' in source
    public=source.split('theorem node ',1)[1]
    assert '(ih ' not in public and 'Local reader (Generated reader) left right ∧ Local reader (Generated reader) right left' in public
    fixture=(HERE/'causal-node-local-kernels.lean').read_text()
    private=fixture.split('private theorem checked :\n',1)[1].split(' := by\n',1)[0]
    public=fixture.split('theorem changed_reference_rows :\n',1)[1].split(' := checked',1)[0]
    assert private==public and '[(10,false),(11,true)]' in public
    assert 'SourceCurrentCausalGeneratedNodeLocal.node' in fixture
    assert m['groups']==s['groups']
    print(json.dumps({'status':'PASS','entries':len(m['entries']),'public_pairs':1,'constructed_pairs':1,'auxiliary_pairs':0,'owned_lean_runs':6},sort_keys=True))
if __name__=='__main__':main()
