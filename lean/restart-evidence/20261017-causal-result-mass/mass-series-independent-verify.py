from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
base = Path(__file__).resolve().parent
source = root / 'lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassSeries.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '521b7186717669eb920ebf8c06b827fa4a4bc49aadf0eca801d04443ef0b6d74'
assert source.read_bytes() == (base / 'mass-series-independent-reviewed.source.lean').read_bytes()
assert source.read_bytes() == (base / 'mass-series-direct-2.source.lean').read_bytes()
assert (base / 'mass-series-direct-2.log').read_bytes() == b''
names = re.findall(r'^(?:def|theorem) ([^\s({:]+)', source.read_text(), re.M)
assert len(names) == 9
public = (base / 'mass-series-independent-public.lean').read_text()
for name in names:
    full = 'MicroCFTA.SourceCurrentAllocatedRecursiveMassSeries.' + name
    assert '#print axioms ' + full + '\n' in public
    assert '#check @' + full + '\n' in public
for stem, pairs, attempt in [('mass-series-independent-public', 9, 1), ('mass-series-independent-kernels', 2, 4)]:
    probe = base / (stem + '.lean')
    assert probe.read_bytes() == (base / (stem + '-' + str(attempt) + '.source.lean')).read_bytes()
    text = probe.read_text()
    assert text.count('#print axioms ') == pairs
    assert text.count('#check @') == pairs
    for option in ['explicit', 'fullNames', 'proofs', 'universes', 'deepTerms']:
        assert 'set_option pp.' + option + ' true\n' in text
    assert 'set_option pp.maxSteps 10000000\n' in text
    assert 'set_option linter.all true\n' in text
    log = (base / (stem + '-' + str(attempt) + '.log')).read_text()
    assert not re.search(r'error(?:\(|:)|warning:|sorryAx', log)
    assert len(re.findall(r'depends on axioms:|does not depend on any axioms', log)) == pairs
    for group in re.findall(r'depends on axioms:\s*\[(.*?)\]', log, re.S):
        for axiom in group.split(','):
            assert re.sub(r'\.\{[^}]*\}', '', axiom.strip()) in {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Build completed successfully (1188 jobs).' in (base / 'canonical-mass-series-1.log').read_text()
for path in [source, base / 'mass-series-independent-public.lean', base / 'mass-series-independent-kernels.lean', base / 'mass-series-independent-review.md']:
    raw = path.read_bytes()
    assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'), path
manifest = base / 'mass-series-independent-manifest.json'
if manifest.exists():
    data = json.loads(manifest.read_text())
    assert len(data['files']) == data['file_count']
    for item in data['files']:
        path = root / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
print('PASS: exact frozen source; 9 public and 2 actual generated-series integration pairs; standard axioms; canonical 1188 jobs.')
