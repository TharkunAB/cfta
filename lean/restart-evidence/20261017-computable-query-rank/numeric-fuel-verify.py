from pathlib import Path
import hashlib, json, re

root = Path(__file__).resolve().parents[3]
base = Path(__file__).resolve().parent
source = root / 'lean/MicroCFTA/IntersectNumericFuel.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '89a842906ae386e1b1da10b99040a321b9db8ba01e98751edbc8bd41ab09cca4'
assert source.read_bytes() == (base / 'numeric-fuel-direct-2.source.lean').read_bytes()
assert (base / 'numeric-fuel-direct-2.log').read_bytes() == b''
names = re.findall(r'^theorem ([^\s({:]+)', source.read_text(), re.M)
assert names == ['call_numeric', 'requiredFuel_le_numeric']
public = (base / 'numeric-fuel-public.lean').read_text()
for name in names:
    full = 'MicroCFTA.IntersectSchedule.' + name
    assert '#print axioms ' + full + '\n' in public
    assert '#check @' + full + '\n' in public
for stem, attempt, pairs in [('numeric-fuel-public', 1, 2), ('numeric-fuel-kernels', 4, 2)]:
    path = base / (stem + '.lean')
    assert path.read_bytes() == (base / f'{stem}-{attempt}.source.lean').read_bytes()
    text = path.read_text()
    assert text.count('#print axioms ') == pairs and text.count('#check @') == pairs
    for option in ['explicit', 'fullNames', 'proofs', 'universes', 'deepTerms']:
        assert f'set_option pp.{option} true\n' in text
    assert 'set_option pp.maxSteps 10000000\n' in text
    assert 'set_option linter.all true\n' in text
    log = (base / f'{stem}-{attempt}.log').read_text()
    assert not re.search(r'error(?:\(|:)|warning:|sorryAx', log)
    assert len(re.findall(r'depends on axioms:|does not depend on any axioms', log)) == pairs
    for group in re.findall(r'depends on axioms:\s*\[(.*?)\]', log, re.S):
        for axiom in group.split(','):
            assert re.sub(r'\.\{[^}]*\}', '', axiom.strip()) in {'propext', 'Classical.choice', 'Quot.sound'}
canonical = (base / 'numeric-fuel-canonical-1.log').read_text()
assert 'Build completed successfully (74 jobs).' in canonical
assert not re.search(r'error(?:\(|:)|warning:|sorryAx', canonical)
for stem, last in [('numeric-fuel-direct', 2), ('numeric-fuel-kernels', 4)]:
    for attempt in range(1, last + 1):
        assert (base / f'{stem}-{attempt}.source.lean').is_file()
        assert (base / f'{stem}-{attempt}.log').is_file()
for path in [source] + [base / ('numeric-fuel-' + suffix) for suffix in ['public.lean', 'kernels.lean', 'review.md', 'validation.json', 'verify.py', 'reproduce.sh']]:
    raw = path.read_bytes()
    assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'), path
manifest = base / 'numeric-fuel-manifest.json'
if manifest.exists():
    data = json.loads(manifest.read_text())
    assert len(data['files']) == data['file_count']
    assert data['public_pairs'] == 2 and data['integration_pairs'] == 2
    for item in data['files']:
        path = root / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
print('PASS: numeric semantic fuel frozen; 2 public and 2 reset/constructed-recursive integration pairs; standard axioms; canonical74.')
