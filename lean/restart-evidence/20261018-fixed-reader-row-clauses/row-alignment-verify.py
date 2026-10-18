import hashlib
import importlib.util
import json
import re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'row-alignment-manifest.json').read_text())
    for e in m['entries']:
        p=ROOT/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],p
    s=json.loads((HERE/'row-alignment-selection.json').read_text())
    assert s['finalized'] and s['owned_lean_runs']==3 and not s['retained_unselected']
    assert [s[k] for k in ['public_pairs','constructed_pairs','auxiliary_pairs']]==[1,0,0]
    assert sha(ROOT/s['production'])==s['sha256']
    assert json.loads((HERE/(s['strict']+'.json')).read_text())['sha256']==s['sha256']
    for stem in [s['strict'],s['canonical']]+[g['name'] for g in s['groups']]:
        meta=json.loads((HERE/(stem+'.json')).read_text());assert meta['exit_code']==0
        assert meta['wrapper']==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(HERE/'row-alignment-capped-worker.py')]
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        if 'source' in meta:assert sha(HERE/meta['source'])==meta['sha256']
    assert not (HERE/(s['strict']+'.log')).read_bytes()
    canonical=(HERE/(s['canonical']+'.log')).read_text()
    assert 'Build completed successfully' in canonical and not re.search(r'warning:|error:',canonical)
    spec=importlib.util.spec_from_file_location('probes',HERE/'row-alignment-probe-check.py')
    p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
    for g in s['groups']:p.check_group(g)
    source=(ROOT/s['production']).read_text()
    assert len(re.findall(r'^(?:def|theorem) ',source,re.M))==1
    assert 'SourceCurrentGeneratedRowSchedules.node' in source
    assert 'SourceCurrentCausalGeneratedEmpty.generated reader history pair.1' in source
    assert 'RowMatch (Mutual (Generated reader)) firstOutput secondOutput' in source
    assert '(oppositeCalls : ∀ original ∈ nodeEdges rawSecond, ∃ output, RowCalls second reader original output)' in source
    assert 'buildEdges expressions' in source and 'firstRow.output = row' in source
    assert 'Local ' not in source and 'Directed ' not in source
    assert m['groups']==s['groups']
    print(json.dumps({'status':'PASS','entries':len(m['entries']),'public_pairs':1,'constructed_pairs':0,'auxiliary_pairs':0,'owned_lean_runs':3},sort_keys=True))
if __name__=='__main__':main()
