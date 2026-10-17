from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / 'stored-rebind-boundary-manifest.json').read_text())
for entry in manifest['entries']:
    path = ROOT / entry['path']
    raw = path.read_bytes()
    assert len(raw) == entry['bytes'], str(path)
    assert hashlib.sha256(raw).hexdigest() == entry['sha256'], str(path)

source = ROOT / manifest['production']['path']
assert source.read_bytes() == (HERE / 'stored-rebind-boundary-direct-3.source.lean').read_bytes()
assert source.read_bytes() == (HERE / 'stored-rebind-boundary-canonical-2.source.lean').read_bytes()
assert (HERE / 'stored-rebind-boundary-direct-3.log').read_bytes() == b''
for stem in ['stored-rebind-boundary-direct-3', 'stored-rebind-boundary-canonical-2',
             'stored-rebind-boundary-public-3', 'stored-rebind-boundary-kernels-3']:
    metadata = json.loads((HERE / (stem + '.json')).read_text())
    assert metadata['exit_code'] == 0, stem
    assert (HERE / (stem + '.caps')).read_text().splitlines() == ['4294967296', '4294967296', '0'], stem
canonical = (HERE / 'stored-rebind-boundary-canonical-2.log').read_text()
assert 'Build completed successfully (260 jobs).' in canonical
assert not re.search(r'warning:|error:|sorryAx', canonical)

options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.universes true', 'pp.deepTerms true', 'pp.proofs.threshold 254',
           'pp.maxSteps 10000000']
groups = [('stored-rebind-boundary-public-3', manifest['public_names'], True),
          ('stored-rebind-boundary-kernels-3', manifest['kernel_names'], False)]
for stem, names, proofs in groups:
    text = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    for option in options:
        assert 'set_option ' + option in text, (stem, option)
    assert not re.search(r': (?:error|warning)(?:\(|:)|\bsorryAx\b|failed to pretty print', log), stem
    axioms = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    assert len(axioms) == len(names) and {name for name, _ in axioms} == set(names), stem
    for name, used in axioms:
        assert '#check @' + name in text and '#print axioms ' + name in text, (stem, name)
        if proofs:
            assert '#print ' + name in text, (stem, name)
        parsed = {part.strip().split('.{')[0] for part in used.split(',') if part.strip()}
        assert parsed <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, parsed)

assert 'failed to pretty print' in (HERE / 'stored-rebind-boundary-public-1.log').read_text()
assert json.loads((HERE / 'stored-rebind-boundary-public-2.json').read_text())['exit_code'] == -15
print('PASS', len(manifest['entries']), 'immutable entries; 1 public + 1 constructed row/unfold pair; '
      'strict empty; canonical260; standard axioms; caps4G/4G/0; failed attempts retained')
