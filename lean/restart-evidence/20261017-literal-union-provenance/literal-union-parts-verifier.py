from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
m=json.loads((HERE/'literal-union-parts-manifest.json').read_text())
for item in m['entries']:
    path=ROOT/item['path']
    data=path.read_bytes()
    assert len(data)==item['bytes'],path
    assert hashlib.sha256(data).hexdigest()==item['sha256'],path
caps={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
for stem in m['selected_runs']:
    meta=json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code']==0,stem
    assert json.loads((HERE/meta['limits']).read_text())==caps,stem
    log=(HERE/meta['log']).read_text()
    assert not re.search(r': (error|warning):',log),stem
    assert 'sorryAx' not in log,stem
    if 'source' in meta:
        data=(HERE/meta['source']).read_bytes()
        assert hashlib.sha256(data).hexdigest()==meta['sha256'],stem
for stem in m['selected_strict']:
    assert (HERE/(stem+'.log')).stat().st_size==0,stem
options=['set_option linter.all true','set_option pp.explicit true','set_option pp.fullNames true','set_option pp.proofs true','set_option pp.proofs.threshold 254','set_option pp.universes true','set_option pp.deepTerms true','set_option pp.maxSteps 10000000']
allowed={'propext','Classical.choice','Quot.sound'}
for group in m['probe_groups']:
    source=(HERE/(group['stem']+'.source.lean')).read_text()
    log=(HERE/(group['stem']+'.log')).read_text()
    for option in options:
        assert option in source,(group,option)
    names=re.findall(r'^#check @([^\n]+)$',source,re.M)
    assert names==group['names'],(group,names)
    for name in names:
        assert '#print '+name+'\n' in source,name
        assert '#print axioms '+name+'\n' in source,name
        match=re.search(re.escape("'"+name+"' depends on axioms: [")+r'(.*?)\]',log,re.S)
        if match:
            axioms={re.sub(r'\.\{[^}]*\}','',a.strip()) for a in match[1].split(',') if a.strip()}
            assert axioms<=allowed,(name,axioms)
        else:
            assert "'"+name+"' does not depend on any axioms" in log,name
for production,snapshot in m['source_snapshots'].items():
    assert (ROOT/production).read_bytes()==(HERE/snapshot).read_bytes(),production
assert len(m['probe_groups'][0]['names'])==2
assert len(m['probe_groups'][1]['names'])==1
print(f"PASS {len(m['entries'])} immutable entries; 2 public +1 constructed pair; empty strict log; standard axioms; caps4G/4G/0")
