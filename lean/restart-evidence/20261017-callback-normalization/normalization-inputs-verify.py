from pathlib import Path
import hashlib, json, re
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'normalization-inputs-manifest.json').read_text())
for entry in manifest['entries']:
    path = ROOT / entry['path']
    data = path.read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
validation = json.loads((HERE / 'normalization-inputs-validation.json').read_text())
assert (HERE / (validation['strict'] + '.log')).stat().st_size == 0
for stem in [validation['strict'], validation['canonical'], validation['public']['stem'], validation['integration']['stem']]:
    metadata = json.loads((HERE / (stem + '.json')).read_text())
    assert metadata['exit_code'] == 0, stem
    assert (HERE / metadata['caps']).read_text().splitlines() == ['4294967296', '4294967296', '0'], stem
    source = ROOT / metadata['source'] if stem == validation['canonical'] else HERE / metadata['source']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == metadata['source_sha256'], stem
options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.proofs.threshold 254', 'pp.maxSteps 10000000']
for key in ['public', 'integration']:
    group = validation[key]
    stem = group['stem']
    source = (HERE / (stem + '.source.lean')).read_text()
    output = (HERE / (stem + '.log')).read_text()
    for option in options:
        assert 'set_option ' + option + '\n' in source, (stem, option)
    assert not re.search(r'error:|error\(|warning:|sorryAx|⋯|declaration uses', output), stem
    assert source.count('#check @') == source.count('#print axioms ') == group['pairs'], stem
    reports = output.count('depends on axioms:') + output.count('does not depend on any axioms')
    assert reports == group['pairs'], (stem, reports)
    if key == 'public':
        assert len(re.findall(r'^#print (?!axioms)', source, re.M)) == group['full_proof_prints']
    for dependencies in re.findall(r'depends on axioms: \[(.*?)\]', output, re.S):
        for name in dependencies.split(','):
            name = re.sub(r'\.\{[^}]*\}', '', name.strip())
            assert name in validation['allowed_axioms'], (stem, name)
assert 'Build completed successfully (278 jobs).' in (HERE / (validation['canonical'] + '.log')).read_text()
production = ROOT / validation['production']
assert production.read_bytes() == (HERE / (validation['strict'] + '.source.lean')).read_bytes()
assert hashlib.sha256(production.read_bytes()).hexdigest() == validation['production_sha256']
for stem in validation['unselected_attempts']:
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] != 0, stem
assert not (HERE / 'normalization-inputs-kernels-3.caps').exists()
assert (HERE / 'normalization-inputs-public.lean').read_bytes() == (HERE / 'normalization-inputs-public-1.source.lean').read_bytes()
assert (HERE / 'normalization-inputs-kernels.lean').read_bytes() == (HERE / 'normalization-inputs-kernels-5.source.lean').read_bytes()
print('PASS', len(manifest['entries']), 'hashed entries; strict empty; canonical278; public8 full proof/axiom groups; integrations2; standard axioms only')
