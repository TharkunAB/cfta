from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
OPTIONS=['set_option linter.all true','set_option pp.explicit true','set_option pp.fullNames true','set_option pp.proofs true','set_option pp.proofs.threshold 254','set_option pp.universes true','set_option pp.deepTerms true','set_option pp.maxSteps 10000000']
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def meta(stem):
    m=json.loads((HERE/(stem+'.json')).read_text())
    assert m['exit_code']==0,stem
    assert json.loads((HERE/m['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},stem
    if 'source' in m:
        assert sha(HERE/m['source'])==m['sha256'],stem
        assert m['command'][-1]==str(HERE/m['source']),stem
    return m
m=json.loads((HERE/'outer-inherited-manifest.json').read_text())
for item in m['entries']:
    path=ROOT/item['path']
    assert path.stat().st_size==item['bytes'],str(path)
    assert sha(path)==item['sha256'],str(path)
for stem in ['outer-inherited-direct-3','outer-inherited-kernels-strict-1']:
    run=meta(stem); assert not (HERE/run['log']).read_bytes(),stem
assert (HERE/'outer-inherited-direct-3.source.lean').read_bytes()==(ROOT/'lean/MicroCFTA/SourceCurrentOuterInheritedDescent.lean').read_bytes()
canonical=meta('outer-inherited-canonical-1')
assert canonical['command'][-1]=='MicroCFTA.SourceCurrentOuterInheritedDescent'
assert 'Build completed successfully (1395 jobs).' in (HERE/canonical['log']).read_text()
for group in m['probe_groups']:
    run=meta(group['stem']); source=(HERE/run['source']).read_text(); log=(HERE/run['log']).read_text()
    assert all(option in source for option in OPTIONS),group['stem']
    assert len(re.findall(r'^#check @',source,re.M))==len(group['names'])
    assert len(re.findall(r'^#print axioms ',source,re.M))==len(group['names'])
    if group['full_proof']:
        assert len(re.findall(r'^#print (?!axioms )',source,re.M))==len(group['names'])
    assert not re.search(r': (?:error|warning)(?:\([^)]*\))?:|sorryAx|failed to pretty print|proof omitted|…|\.\.\.',log),group['stem']
    for name in group['names']:
        if "'"+name+"' does not depend on any axioms" in log: continue
        found=re.search(re.escape("'"+name+"' depends on axioms: [")+r'(.*?)\]',log,re.S)
        assert found,(group['stem'],name)
        axioms={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in found[1].split(',') if x.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
kernels=(HERE/'outer-inherited-kernels-3.source.lean').read_text()
stripped='\n'.join(line for line in kernels.split('\n') if not line.startswith(('#check','#print')))
assert stripped==(HERE/'outer-inherited-kernels-strict-1.source.lean').read_text()
for required in ['descend_lt 0 [record]','node_key_ne 0 [record]','secondRunning.nodeResults.cells 0','secondRunning.nodeResults.cells 1','warm = (descended.1,secondRunning)','SourceEqualityConstraintMemoAllocation.descend last.1 19 last.2']:
    assert required in kernels,required
for stem in ['outer-inherited-direct-1','outer-inherited-direct-2','outer-inherited-kernels-1','outer-inherited-kernels-2']:
    assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']!=0,stem
print(f"PASS {len(m['entries'])} immutable entries; canonical1395; 6 public + 2 constructed pairs; strict EMPTY; standard axioms; caps4G/4G/0")
