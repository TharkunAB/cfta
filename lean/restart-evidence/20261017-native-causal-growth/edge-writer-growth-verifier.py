from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/tritlo/Code/mcfta')
HERE=Path(__file__).resolve().parent
manifest=json.loads((HERE/'edge-writer-growth-manifest.json').read_text())
for entry in manifest['entries']:
    data=(ROOT/entry['path']).read_bytes()
    assert len(data)==entry['bytes'],entry['path']
    assert hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
assert (ROOT/manifest['production']['path']).read_bytes()==(HERE/'edge-writer-growth-direct-1.source.lean').read_bytes()
assert not (HERE/'edge-writer-growth-direct-1.log').read_bytes()
for metadata in HERE.glob('edge-writer-growth-*.json'):
    record=json.loads(metadata.read_text())
    if 'command' not in record: continue
    assert record['exit_code']==0,metadata.name
    caps=json.loads((HERE/record['limits']).read_text())
    assert caps=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},metadata.name
    if 'source' in record:
        source=HERE/record['source']
        assert hashlib.sha256(source.read_bytes()).hexdigest()==record['sha256'],metadata.name
        assert record['command'][-1]==str(source),metadata.name
        assert '-Dlinter.all=true' in record['command'],metadata.name
allowed={'propext','Classical.choice','Quot.sound'}
for stem,count in [('edge-writer-growth-public-1',11),('edge-writer-growth-kernels-1',1)]:
    source=(HERE/(stem+'.source.lean')).read_text()
    log=(HERE/(stem+'.log')).read_text()
    assert not re.search(r'\b(?:error|warning)(?:\(|:)|sorryAx|\bsorry\b|failed to pretty print',log,re.I),stem
    targets=re.findall(r'^#check @([^\s]+)',source,re.M)
    prints=re.findall(r'^#print (?!axioms )([^\s]+)',source,re.M)
    axioms=re.findall(r'^#print axioms ([^\s]+)',source,re.M)
    assert len(targets)==len(set(targets))==count,stem
    assert targets==prints==axioms,stem
    for setting in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+setting in source,(stem,setting)
    results=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",log,re.S)
    assert [r[0] for r in results]==targets,(stem,[r[0] for r in results])
    for target,names,empty in results:
        for name in names.split(','):
            if name.strip(): assert re.sub(r'\.\{[^}]*\}','',name.strip()) in allowed,(target,name)
assert 'Build completed successfully (1168 jobs).' in (HERE/'edge-writer-growth-canonical-1.log').read_text()
source=(ROOT/manifest['production']['path']).read_text()
assert not re.search(r'\b(?:sorry|axiom)\b|set_option linter\.[^ ]+ false',source)
assert (HERE/'edge-writer-growth-kernels.lean').read_bytes()==(HERE/'edge-writer-growth-kernels-1.source.lean').read_bytes()
print(f'PASS {len(manifest["entries"])} immutable entries; public11 + integration1 =12 pairs; strict EMPTY; std3; actual4GiB/4GiB/zeroSwap; full printer output')
