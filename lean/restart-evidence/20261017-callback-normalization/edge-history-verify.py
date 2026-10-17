from pathlib import Path
import hashlib, json, re
ROOT=Path('/home/tritlo/Code/mcfta')
HERE=Path(__file__).resolve().parent
manifest=json.loads((HERE/'edge-history-manifest.json').read_text())
for entry in manifest['entries']:
    data=(ROOT/entry['path']).read_bytes()
    assert len(data)==entry['bytes'],entry['path']
    assert hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
assert (ROOT/'lean/MicroCFTA/SourceCurrentNativeEdgeHistory.lean').read_bytes()==(HERE/'edge-history-direct-15.source.lean').read_bytes()
assert not (HERE/'edge-history-direct-15.log').read_bytes()
assert json.loads((HERE/'edge-history-direct-15.json').read_text())['exit_code']==0
for metadata in HERE.glob('edge-history-*.json'):
    if metadata.name=='edge-history-manifest.json': continue
    record=json.loads(metadata.read_text())
    if 'source_sha256' in record:
        assert hashlib.sha256((HERE/record['source']).read_bytes()).hexdigest()==record['source_sha256'],metadata.name
        assert (HERE/record['log']).is_file(),metadata.name
allowed={'propext','Classical.choice','Quot.sound'}
for stem,count in [('edge-history-public-1',6),('edge-history-kernels-2',2)]:
    source=(HERE/(stem+'.source.lean')).read_text()
    log=(HERE/(stem+'.log')).read_text()
    assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0
    assert not re.search(r'\b(?:error|warning)(?:\(|:)|sorryAx|basename:',log)
    targets=re.findall(r'^#check @([^\s]+)',source,re.M)
    prints=re.findall(r'^#print (?!axioms )([^\s]+)',source,re.M)
    axioms=re.findall(r'^#print axioms ([^\s]+)',source,re.M)
    assert len(targets)==len(set(targets))==count
    assert targets==prints==axioms
    for setting in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+setting in source,(stem,setting)
    results=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",log,re.S)
    assert [r[0] for r in results]==targets
    for target,names,empty in results:
        for name in names.split(','):
            if name.strip(): assert re.sub(r'\.\{[^}]*\}','',name.strip()) in allowed,(target,name)
for stem in ['edge-history-direct-15','edge-history-public-1','edge-history-kernels-2']:
    assert (HERE/(stem+'.caps')).read_text()=='4294967296\n4294967296\n0\n'
canonical=(HERE/'edge-history-canonical-1.log').read_text()
assert canonical.startswith('4294967296\n4294967296\n0\n')
assert 'Build completed successfully (1114 jobs).' in canonical
source=(ROOT/'lean/MicroCFTA/SourceCurrentNativeEdgeHistory.lean').read_text()
assert not re.search(r'\b(?:sorry|axiom)\b|set_option linter\.[^ ]+ false',source)
print(f'PASS {len(manifest["entries"])} immutable entries; public 6 + integration 2 = 8 pairs; strict EMPTY; standard axioms; actual 4GiB/4GiB/zeroSwap')
