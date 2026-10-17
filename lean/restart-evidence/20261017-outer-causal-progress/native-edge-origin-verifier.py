from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/tritlo/Code/mcfta')
HERE=Path(__file__).resolve().parent
manifest=json.loads((HERE/'native-edge-origin-manifest.json').read_text())
for entry in manifest['entries']:
    data=(ROOT/entry['path']).read_bytes()
    assert len(data)==entry['bytes'],entry['path']
    assert hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
for production,stem in [
    ('SourceCurrentNativeEdgeWriterHistory','native-edge-writer-history-direct-5'),
    ('SourceCurrentNativeOwnOriginBoundary','native-own-origin-boundary-direct-3')]:
    assert (ROOT/('lean/MicroCFTA/'+production+'.lean')).read_bytes()==(HERE/(stem+'.source.lean')).read_bytes()
    assert not (HERE/(stem+'.log')).read_bytes(),stem
for metadata in HERE.glob('native*.json'):
    record=json.loads(metadata.read_text())
    if 'command' not in record: continue
    assert (HERE/record['log']).is_file(),metadata.name
    if 'source' in record:
        source=HERE/record['source']
        assert hashlib.sha256(source.read_bytes()).hexdigest()==record['sha256'],metadata.name
        assert record['command'][-1]==str(source),metadata.name
        assert '-Dlinter.all=true' in record['command'],metadata.name
    if 'limits' in record:
        caps=json.loads((HERE/record['limits']).read_text())
        assert caps=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},metadata.name
allowed={'propext','Classical.choice','Quot.sound'}
for stem,count in [('native-edge-writer-history-public-1',8),('native-own-origin-boundary-public-1',1),('native-edge-writer-history-kernels-2',1)]:
    source=(HERE/(stem+'.source.lean')).read_text()
    log=(HERE/(stem+'.log')).read_text()
    assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0,stem
    assert not re.search(r'\b(?:error|warning)(?:\(|:)|sorryAx|\bsorry\b',log),stem
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
for stem in manifest['selected']['strict']+manifest['selected']['canonical']:
    assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0,stem
for stem in manifest['selected']['canonical']:
    assert 'Build completed successfully' in (HERE/(stem+'.log')).read_text(),stem
for item in manifest['productions']:
    source=(ROOT/item['path']).read_text()
    assert not re.search(r'\b(?:sorry|axiom)\b|set_option linter\.[^ ]+ false',source),item['path']
assert (HERE/'native-edge-writer-history-kernels.lean').read_bytes()==(HERE/'native-edge-writer-history-kernels-2.source.lean').read_bytes()
print(f'PASS {len(manifest["entries"])} immutable entries; public9 + integration1 =10 pairs; strict EMPTY; std3; actual4GiB/4GiB/zeroSwap')
