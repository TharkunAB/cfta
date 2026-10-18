import hashlib
import importlib.util
import json
import re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    m=json.loads((HERE/'union-fixed-reader-manifest.json').read_text())
    for e in m['entries']:
        p=ROOT/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],p
    s=json.loads((HERE/'union-fixed-reader-selection.json').read_text())
    assert s['finalized'] and s['owned_lean_runs']==9
    assert [s[k] for k in ['public_pairs','constructed_pairs','auxiliary_pairs']]==[1,1,0]
    assert sha(ROOT/s['production'])==s['sha256']
    assert json.loads((HERE/(s['strict']+'.json')).read_text())['sha256']==s['sha256']
    stems=[s['strict'],s['canonical'],s['constructed_strict']]+[g['name'] for g in s['groups']]+[a['stem'] for a in s['retained_unselected']]
    failed={a['stem'] for a in s['retained_unselected']}
    assert len(stems)==9 and len(set(stems))==9
    for stem in stems:
        meta=json.loads((HERE/(stem+'.json')).read_text())
        assert meta['exit_code']==(1 if stem in failed else 0)
        assert meta['wrapper']==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(HERE/'union-fixed-reader-capped-worker.py')]
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        if 'source' in meta:assert sha(HERE/meta['source'])==meta['sha256']
    for stem in [s['strict'],s['constructed_strict']]:assert not (HERE/(stem+'.log')).read_bytes()
    canonical=(HERE/(s['canonical']+'.log')).read_text()
    assert 'Build completed successfully' in canonical and not re.search(r'warning:|error:',canonical)
    spec=importlib.util.spec_from_file_location('probes',HERE/'union-fixed-reader-probe-check.py')
    p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
    for g in s['groups']:p.check_group(g)
    source=(ROOT/s['production']).read_text()
    assert len(re.findall(r'^(?:def|theorem) ',source,re.M))==1
    assert 'theorem source ' in source
    assert 'SourceCurrentGeneratedUnionPreparation.source_members' in source
    assert 'SourceCurrentStoredLiteralExecutionParts.atom' in source and 'SourceCurrentStoredLiteralExecutionParts.row' in source
    assert 'SourceCurrentStoredLiteralExecutionParts.parts' in source
    assert '(raw = .reference own ∨ source ≠ .reference own)' in source
    assert '∃ output, RowCalls environment reader original output' in source
    assert 'Keeps ' not in source and 'Same ' not in source and 'Directed ' not in source
    assert m['groups']==s['groups']
    print(json.dumps({'status':'PASS','entries':len(m['entries']),'public_pairs':1,'constructed_pairs':1,'auxiliary_pairs':0,'owned_lean_runs':9},sort_keys=True))
if __name__=='__main__':main()
