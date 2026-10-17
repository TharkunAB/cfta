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
    assert sha(HERE/m['source'])==m['sha256'],stem
    assert m['command'][-1]==str(HERE/m['source']),stem
    return m
m=json.loads((HERE/'writer-boundary-manifest.json').read_text())
for item in m['entries']:
    path=ROOT/item['path']
    assert path.stat().st_size==item['bytes'],str(path)
    assert sha(path)==item['sha256'],str(path)
for group in m['probe_groups']:
    run=meta(group['stem']); source=(HERE/run['source']).read_text(); log=(HERE/run['log']).read_text()
    assert all(option in source for option in OPTIONS),group['stem']
    assert len(re.findall(r'^#check @',source,re.M))==len(group['names'])
    assert len(re.findall(r'^#print axioms ',source,re.M))==len(group['names'])
    assert not re.search(r': (?:error|warning)(?:\([^)]*\))?:|sorryAx|failed to pretty print|proof omitted|…|\.\.\.',log),group['stem']
    for name in group['names']:
        found=re.search(re.escape("'"+name+"' depends on axioms: [")+r'(.*?)\]',log,re.S)
        assert found,(group['stem'],name)
        axioms={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in found[1].split(',') if x.strip()}
        assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)
strict=meta('writer-boundary-strict-1')
assert not (HERE/strict['log']).read_bytes()
sources=[(HERE/'writer-boundary-filter-2.source.lean').read_text(),(HERE/'writer-boundary-smart-3.source.lean').read_text()]
imports=list(dict.fromkeys(line for source in sources for line in source.splitlines() if line.startswith('import ')))
body=['\n'.join(line for line in source.splitlines() if not line.startswith(('import ','#check ','#print '))) for source in sources]
assert (HERE/strict['source']).read_text()=='\n'.join(imports)+'\n\n'+'\n'.join(body)+'\n'
filterSource,smartSource=sources
for required in ['SourceCurrentOpenObservationSurvival.Related first.1 second.1','first.1.free = second.1.free','InternedDeepFreeDepth.deepNames first.1 = InternedDeepFreeDepth.deepNames second.1','first.1.depth = second.1.depth','∀ marker, first.1 ≠ .reference marker','withoutSelfReference name first.1','withoutSelfReference name second.1']:
    assert required in filterSource,required
for required in ['build firstExpression [] middle = .done firstValue middle','∀ name, Available middle (.reference name)','Related (raw name).1 (.reference name)','¬ Related firstValue secondValue']:
    assert required in smartSource,required
assert json.loads((HERE/'writer-boundary-filter-1.json').read_text())['exit_code']!=0
assert json.loads((HERE/'writer-boundary-smart-1.json').read_text())['exit_code']!=0
print(f"PASS {len(m['entries'])} immutable entries; 2 source-built pairs; strict EMPTY; standard axioms; caps4G/4G/0")
