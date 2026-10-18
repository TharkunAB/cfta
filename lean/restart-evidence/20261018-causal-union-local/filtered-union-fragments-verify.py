import hashlib
import importlib.util
import json
import re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'filtered-union-fragments-manifest.json').read_text())
    for e in m['entries']:
        p=ROOT/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],p
    s=json.loads((HERE/'filtered-union-fragments-selection.json').read_text())
    assert s['finalized'] and s['owned_lean_runs']==6
    assert [s[k] for k in ['public_pairs','constructed_pairs','auxiliary_pairs']]==[1,0,0]
    assert sha(ROOT/s['production'])==s['sha256']
    assert json.loads((HERE/(s['strict']+'.json')).read_text())['sha256']==s['sha256']
    stems=[s['strict'],s['canonical']]+[g['name'] for g in s['groups']]+[a['stem'] for a in s['retained_unselected']]
    failed={a['stem'] for a in s['retained_unselected']}
    for stem in stems:
        meta=json.loads((HERE/(stem+'.json')).read_text())
        assert meta['exit_code']==(1 if stem in failed else 0)
        assert meta['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        if 'source' in meta:assert sha(HERE/meta['source'])==meta['sha256']
    assert not (HERE/(s['strict']+'.log')).read_bytes()
    canonical=(HERE/(s['canonical']+'.log')).read_text()
    assert 'Build completed successfully' in canonical and not re.search(r'warning:|error:',canonical)
    spec=importlib.util.spec_from_file_location('probes',HERE/'filtered-union-fragments-probe-check.py')
    p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
    for g in s['groups']:p.check_group(g)
    source=(ROOT/s['production']).read_text()
    assert source.count('\ntheorem ')==1
    assert 'SourceCurrentFilteredUnionCoverage.parts' in source
    assert source.count('(raw ≠ .reference own ∨ parent = .reference own)')==2
    assert 'filters[index]? = some cut ∧ outputs[index]? = some output' in source
    assert m['groups']==s['groups']
    print(json.dumps({'status':'PASS','entries':len(m['entries']),'public_pairs':1,'constructed_pairs':0,'auxiliary_pairs':0,'owned_lean_runs':6},sort_keys=True))
if __name__=='__main__':main()
