import hashlib
import importlib.util
import json
import re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'row-alignment-integration-manifest.json').read_text())
    for e in m['entries']:
        p=ROOT/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],p
    s=json.loads((HERE/'row-alignment-integration-selection.json').read_text())
    assert s['finalized'] and s['owned_lean_runs']==2 and not s['retained_unselected']
    assert [s[k] for k in ['public_pairs','constructed_pairs','auxiliary_pairs']]==[0,1,0]
    assert sha(ROOT/s['fixture'])==s['sha256']
    assert json.loads((HERE/(s['strict']+'.json')).read_text())['sha256']==s['sha256']
    for stem in [s['strict']]+[g['name'] for g in s['groups']]:
        meta=json.loads((HERE/(stem+'.json')).read_text());assert meta['exit_code']==0
        assert meta['wrapper']==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(HERE/'row-alignment-integration-capped-worker.py')]
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        assert sha(HERE/meta['source'])==meta['sha256']
    assert not (HERE/(s['strict']+'.log')).read_bytes()
    canonical=(HERE/(s['canonical_reused']+'.log')).read_text()
    assert 'Build completed successfully' in canonical and not re.search(r'warning:|error:',canonical)
    spec=importlib.util.spec_from_file_location('probes',HERE/'row-alignment-integration-probe-check.py')
    p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
    for g in s['groups']:p.check_group(g)
    source=(ROOT/s['fixture']).read_text()
    assert len(re.findall(r'^theorem ',source,re.M))==1
    assert 'SourceCurrentCausalRowFragmentAlignment.node' in source
    assert 'SourceCurrentFixedReaderUnionFragments.source' in source
    assert 'SourceCurrentNativeMuPublication.build_history source [] empty' in source
    assert 'reader.nodes.next < (execute subgroup emptyDepth reader).state.nodes.next' in source
    assert 'reader.nodes.next < (run (withoutSelfReference .depth subgroup) reader).2.nodes.next' in source
    assert m['groups']==s['groups']
    print(json.dumps({'status':'PASS','entries':len(m['entries']),'public_pairs':0,'constructed_pairs':1,'auxiliary_pairs':0,'owned_lean_runs':2},sort_keys=True))
if __name__=='__main__':main()
