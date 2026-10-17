from pathlib import Path
import hashlib, json, re

root = Path(__file__).resolve().parents[3]
base = Path(__file__).resolve().parent
sources = [
    ('SourceRecursiveIntersectionCompileInstructionCredit', '0a65f659bea3d07ab6aa39f9934be8b17346e7f481c9f0f01c20edc5483ced13', 'compile-cost-direct-6', 7, 1177, 'compile-instruction-credit-canonical-1.log'),
    ('SourceEqualityNativeCheckedInstructionCredit', '7c58a31e6c343aa302454b3a99420eae3d5be80a0356a3e29b0005da545d032e', 'checked-cost-direct-3', 3, 1189, 'checked-instruction-credit-canonical-1.log'),
]
public = (base / 'compile-cost-public.lean').read_text()
for module, expected, direct, count, jobs, canonical in sources:
    source = root / 'lean/MicroCFTA' / (module + '.lean')
    assert hashlib.sha256(source.read_bytes()).hexdigest() == expected
    assert source.read_bytes() == (base / (direct + '.source.lean')).read_bytes()
    assert (base / (direct + '.log')).read_bytes() == b''
    names = re.findall(r'^theorem ([^\s({:]+)', source.read_text(), re.M)
    assert len(names) == count
    for name in names:
        full = 'MicroCFTA.' + module + '.' + name
        assert '#print axioms ' + full + '\n' in public
        assert '#check @' + full + '\n' in public
    canonical_text = (base / canonical).read_text()
    assert f'Build completed successfully ({jobs} jobs).' in canonical_text
    assert not re.search(r'error(?:\(|:)|sorryAx', canonical_text)
    warnings = re.findall(r'^warning: (.*)$', canonical_text, re.M)
    assert warnings == ['MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.']
for stem, attempt, pairs in [('compile-cost-public', 1, 10), ('compile-cost-kernels', 4, 2)]:
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
for stem, last in [('compile-cost-direct', 6), ('checked-cost-direct', 3), ('compile-cost-kernels', 4)]:
    for attempt in range(1, last + 1):
        assert (base / f'{stem}-{attempt}.source.lean').is_file()
        assert (base / f'{stem}-{attempt}.log').is_file()
for path in [root / 'lean/MicroCFTA' / (x[0] + '.lean') for x in sources] + [base / ('compile-cost-' + suffix) for suffix in ['public.lean', 'kernels.lean', 'review.md', 'validation.json', 'verify.py', 'reproduce.sh']]:
    raw = path.read_bytes()
    assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'), path
manifest = base / 'compile-cost-manifest.json'
if manifest.exists():
    data = json.loads(manifest.read_text())
    assert len(data['files']) == data['file_count']
    assert data['public_pairs'] == 10 and data['integration_pairs'] == 2
    for item in data['files']:
        path = root / item['path']
        assert path.stat().st_size == item['bytes'], path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], path
print('PASS: compiler credit frozen; 10 public and 2 constructed-source/actual-body pairs; standard axioms; canonical1177/1189.')
