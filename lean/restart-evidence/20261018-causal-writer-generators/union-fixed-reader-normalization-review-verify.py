import hashlib
import importlib.util
import json
import re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'union-fixed-reader-normalization-review-manifest.json').read_text())
    for e in m['entries']:
        p=ROOT/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],p
    s=json.loads((HERE/'union-fixed-reader-normalization-review-selection.json').read_text())
    assert s['owned_lean_runs']==s['owned_public_pairs']==0 and s['reused_public_pairs']==4
    assert sha(ROOT/s['production'])==s['sha256']
    for stem in [s['strict'],s['canonical']]+[g['name'] for g in s['groups']]:
        r=json.loads((HERE/(stem+'.json')).read_text());assert r['exit_code']==0
        assert r['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
        assert json.loads((HERE/r['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        if 'source' in r:assert sha(HERE/r['source'])==r['sha256']
    assert not (HERE/(s['strict']+'.log')).read_bytes()
    c=(HERE/(s['canonical']+'.log')).read_text()
    assert 'Build completed successfully' in c and not re.search(r'warning:|error:',c)
    spec=importlib.util.spec_from_file_location('p',HERE/'union-fixed-reader-probe-check.py')
    checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    for g in s['groups']:checker.check_group(g)
    assert m['groups']==s['groups']
    print(json.dumps(dict(status='PASS',entries=len(m['entries']),owned_lean_runs=0,owned_public_pairs=0,reused_public_pairs=4,reused_constructed_pairs=0),sort_keys=True))
if __name__=='__main__':main()
