from pathlib import Path
import hashlib, json, re
ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE/'mu-publication-manifest.json').read_text())
for item in manifest['entries']:
    path = ROOT/item['path']
    raw = path.read_bytes()
    assert len(raw) == item['bytes'], str(path)
    assert hashlib.sha256(raw).hexdigest() == item['sha256'], str(path)
production = ROOT/manifest['production']['path']
assert production.read_bytes() == (HERE/'mu-publication-direct-9.source.lean').read_bytes()
assert (HERE/'mu-publication-direct-9.log').read_bytes() == b''
for stem in ['mu-publication-direct-9','mu-publication-canonical-1','mu-publication-public-1','mu-publication-kernels-2']:
    meta = json.loads((HERE/(stem+'.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert (HERE/(stem+'.caps')).read_text().splitlines() == ['4294967296','4294967296','0'], stem
assert 'Build completed successfully (271 jobs).' in (HERE/'mu-publication-canonical-1.log').read_text()
allowed = {'propext','Classical.choice','Quot.sound'}
for stem, names in [('mu-publication-public-1',manifest['public_names']),('mu-publication-kernels-2',manifest['kernel_names'])]:
    raw = (HERE/(stem+'.log')).read_text()
    source = (HERE/(stem+'.source.lean')).read_text()
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+option in source, (stem,option)
    assert not re.search(r': (?:error|warning)(?:\(|:)',raw), stem
    assert not re.search(r'\b(?:sorryAx|sorry|admit)\b',raw), stem
    axioms = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
    assert len(axioms) == len(names), (stem,len(axioms),len(names))
    assert {name for name,_ in axioms} == set(names), stem
    for name, ax in axioms:
        values = {item.strip().split('.{')[0] for item in ax.split(',') if item.strip()}
        assert values <= allowed, (name,values)
        assert '#check @'+name in source, name
        assert '#print '+name in source, name
        assert '#print axioms '+name in source, name
print('PASS',len(manifest['entries']),'immutable entries; 42 public + 2 constructed pairs; standard axioms; caps 4G/4G/0')
