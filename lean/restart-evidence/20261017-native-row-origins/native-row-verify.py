from pathlib import Path
import hashlib, json, re
ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE/'native-row-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT/entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
source = ROOT/'lean/MicroCFTA/SourceCurrentNativeRowOrigins.lean'
assert source.read_bytes() == (HERE/'native-row-direct-7.source.lean').read_bytes()
assert not re.search(r'\b(sorry|axiom)\b|set_option linter\.[^ ]+ false',source.read_text())
strict = json.loads((HERE/'native-row-direct-7.json').read_text())
assert strict['exit_code'] == 0
assert not (HERE/'native-row-direct-7.log').read_bytes()
allowed = {'propext','Classical.choice','Quot.sound'}
for stem, count in [('native-row-public-2',5),('native-row-kernels-8',2)]:
    src = (HERE/(stem+'.source.lean')).read_text()
    log = (HERE/(stem+'.log')).read_text()
    meta = json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code'] == 0
    assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest() == meta['source_sha256']
    assert not re.search(r'\b(?:error|warning)(?:\(|:)|sorryAx|basename:',log)
    targets = re.findall(r'^#check @([^\s]+)',src,re.M)
    prints = re.findall(r'^#print (?!axioms )([^\s]+)',src,re.M)
    axioms = re.findall(r'^#print axioms ([^\s]+)',src,re.M)
    assert len(targets) == len(set(targets)) == count
    assert targets == prints == axioms
    for setting in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
                    'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+setting in src, (stem,setting)
    results = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",log,re.S)
    assert [r[0] for r in results] == targets
    for target, names, empty in results:
        for name in names.split(','):
            if name.strip():
                assert re.sub(r'\.\{[^}]*\}', '',name.strip()) in allowed, (target,name)
for stem in ['native-row-direct-7','native-row-public-2','native-row-kernels-8']:
    assert (HERE/(stem+'.caps')).read_text() == '4294967296\n4294967296\n0\n'
canonical = (HERE/'native-row-canonical-1.log').read_text()
assert canonical.startswith('4294967296\n4294967296\n0\n')
assert 'Build completed successfully (1107 jobs).' in canonical
assert json.loads((HERE/'native-row-kernels-1.json').read_text())['exit_code'] == 143
print(f'PASS {len(manifest["entries"])} immutable entries; public 5 + integration 2 = 7 pairs; strict empty; standard axioms only; actual 4GiB/4GiB/zero-swap caps')
