import hashlib
import importlib.util
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'causal-source-review-manifest.json').read_text())
    for e in m['entries']:
        p=ROOT/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],p
    s=json.loads((HERE/'causal-source-review-selection.json').read_text())
    assert s['finalized'] and s['owned_lean_runs']==s['owned_pairs']==0
    assert s['reused_public_pairs']==15 and s['reused_constructed_pairs']==0
    spec=importlib.util.spec_from_file_location('probes',HERE/'causal-source-review-probe-check.py')
    p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
    for g in s['reused_groups']:p.check_group(g)
    assert m['reused_groups']==s['reused_groups']
    print(json.dumps({'status':'PASS','entries':len(m['entries']),'owned_lean_runs':0,'owned_pairs':0,'reused_public_pairs':15,'reused_constructed_pairs':0},sort_keys=True))
if __name__=='__main__':main()
