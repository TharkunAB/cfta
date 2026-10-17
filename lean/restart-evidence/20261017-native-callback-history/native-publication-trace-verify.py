from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'native-publication-trace-manifest.json').read_text())

for entry in manifest['entries']:
    path = ROOT / entry['path']
    raw = path.read_bytes()
    assert len(raw) == entry['bytes'], str(path)
    assert hashlib.sha256(raw).hexdigest() == entry['sha256'], str(path)

production = ROOT / manifest['production']['path']
assert production.read_bytes() == (HERE / 'native-publication-trace-direct-2.source.lean').read_bytes()
assert (HERE / 'native-publication-trace-direct-2.log').read_bytes() == b''

selected = ['native-publication-trace-direct-2', 'native-publication-trace-canonical-1',
            'native-publication-trace-public-1', 'native-publication-trace-kernels-2']
for stem in selected:
    metadata = json.loads((HERE / (stem + '.json')).read_text())
    assert metadata['exit_code'] == 0, stem
    assert (HERE / (stem + '.caps')).read_text().splitlines() == ['4294967296', '4294967296', '0'], stem
canonical = (HERE / 'native-publication-trace-canonical-1.log').read_text()
assert 'Build completed successfully (1118 jobs).' in canonical
assert 'error:' not in canonical and 'sorryAx' not in canonical
assert len(re.findall(r'^warning:', canonical, re.MULTILINE)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24' in canonical

options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.universes true', 'pp.deepTerms true', 'pp.proofs.threshold 254',
           'pp.maxSteps 10000000']
groups = [('native-publication-trace-public-1', manifest['public_names'], True),
          ('native-publication-trace-kernels-2', manifest['kernel_names'], False)]
for stem, names, proof_prints in groups:
    source = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    for option in options:
        assert 'set_option ' + option in source, (stem, option)
    assert not re.search(r': (?:error|warning)(?:\(|:)|\bsorryAx\b', log), stem
    axioms = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    assert len(axioms) == len(names), stem
    assert {name for name, _ in axioms} == set(names), stem
    for name, used in axioms:
        assert '#check @' + name in source, (stem, name)
        assert '#print axioms ' + name in source, (stem, name)
        if proof_prints:
            assert '#print ' + name in source, (stem, name)
        parsed = {item.strip().split('.{')[0] for item in used.split(',') if item.strip()}
        assert parsed <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, parsed)

print('PASS', len(manifest['entries']), 'immutable entries; 9 public + 2 constructed pairs; '
      'strict empty; standard axioms; caps 4G/4G/0; canonical 1118 with one recorded inherited warning')
