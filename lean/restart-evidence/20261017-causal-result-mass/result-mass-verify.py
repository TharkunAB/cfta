from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
base = Path(__file__).resolve().parent
source = root / 'lean/MicroCFTA/InternedFreshOrdinaryResultMass.lean'
expected = '66d5a6719aa4683eb14e86957fe257efd9f6251c3a094ac5cf72fd57d93050df'
assert hashlib.sha256(source.read_bytes()).hexdigest() == expected
assert source.read_bytes() == (base / 'result-mass-direct-2.source.lean').read_bytes()
assert (base / 'result-mass-direct-2.log').read_bytes() == b''
names = re.findall(r'^(?:def|theorem) ([^\s({:]+)', source.read_text(), re.M)
assert len(names) == 15
public = (base / 'result-mass-public.lean').read_text()
for name in names:
    full = 'MicroCFTA.InternedFreshOrdinaryResultMass.' + name
    assert '#print axioms ' + full + '\n' in public
    assert '#check @' + full + '\n' in public
for stem, pairs, log in [
    ('result-mass-public', 15, 'result-mass-public-1.log'),
    ('result-mass-kernels', 3, 'result-mass-kernels-2.log'),
]:
    probe = (base / (stem + '.lean')).read_text()
    for option in ['explicit', 'fullNames', 'proofs', 'universes', 'deepTerms']:
        assert 'set_option pp.' + option + ' true\n' in probe
    assert 'set_option pp.maxSteps 10000000\n' in probe
    assert 'set_option linter.all true\n' in probe
    checked = (base / log).read_text()
    assert not re.search(r'error(?:\(|:)|warning:|sorryAx', checked)
    assert len(re.findall(r'depends on axioms:|does not depend on any axioms', checked)) == pairs
    axioms = re.findall(r'depends on axioms:\s*\[(.*?)\]', checked, re.S)
    for group in axioms:
        for axiom in group.split(','):
            assert re.sub(r'\.\{[^}]*\}', '', axiom.strip()) in {
                'propext', 'Classical.choice', 'Quot.sound'
            }
    assert probe.count('#print axioms ') == pairs
    assert probe.count('#check @') == pairs
assert (base / 'result-mass-public.lean').read_bytes() == (base / 'result-mass-public-1.source.lean').read_bytes()
assert (base / 'result-mass-kernels.lean').read_bytes() == (base / 'result-mass-kernels-2.source.lean').read_bytes()
canonical = (base / 'canonical-result-and-uniform-mass-1.log').read_text()
assert 'Build completed successfully (1183 jobs).' in canonical
for path in [source, base / 'result-mass-public.lean', base / 'result-mass-kernels.lean', base / 'result-mass-review.md']:
    raw = path.read_bytes()
    assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'), path
manifest = base / 'result-mass-manifest.json'
if manifest.exists():
    data = json.loads(manifest.read_text())
    assert len(data['files']) == data['file_count']
    for item in data['files']:
        path = root / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
print('PASS: frozen production; 15 public and 3 integration pairs; standard axioms; exact snapshots; canonical 1183 jobs.')
