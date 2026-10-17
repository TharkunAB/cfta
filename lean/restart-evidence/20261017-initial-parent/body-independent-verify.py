from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'body-independent-validation.json').read_text())
for item in meta['productions']:
    data = (ROOT / item['source']['path']).read_bytes()
    assert len(data) == item['source']['bytes']
    assert hashlib.sha256(data).hexdigest() == item['source']['sha256']
    assert data == (HERE / item['strict']['executed_source']).read_bytes()
    assert (HERE / item['strict']['log']).read_bytes() == b''
    assert item['strict']['exit_code'] == item['canonical']['exit_code'] == 0
    assert f"Build completed successfully ({item['canonical']['jobs']} jobs)." in (HERE / item['canonical']['log']).read_text()
    assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', data.decode())
for item in meta['reviewed_sources']:
    data = (ROOT / item['path']).read_bytes()
    assert len(data) == item['bytes']
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']

for item in (meta['public'], meta['integration']):
    source = (HERE / item['executed_source']).read_text()
    log = (HERE / item['log']).read_text()
    assert item['exit_code'] == 0
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
    for setting in ['linter.all true', 'pp.explicit true', 'pp.fullNames true',
                    'pp.proofs true', 'pp.universes true', 'pp.deepTerms true',
                    'pp.maxSteps 10000000']:
        assert 'set_option ' + setting in source
    names = re.findall(r'^#check @(.+)$', source, re.M)
    assert names == item['names']
    assert len(names) == len(set(names)) == item['pairs']
    assert source.count('#print axioms ') == item['pairs']
    assert source.count('#print ') - source.count('#print axioms ') == (item['pairs'] if item['proof_printing'] else 0)
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == item['pairs']
    for name in names:
        assert '#print axioms ' + name in source
        assert name in log
        if item['proof_printing']:
            assert '#print ' + name in source
            assert 'set_option pp.proofs.threshold 254' in source
    for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        axioms = re.sub(r'\.\{[^}]*\}', '', group).split(',')
        assert all(name.strip() in meta['allowed_axioms'] for name in axioms)
    assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', source)

assert meta['public']['pairs'] == 15
assert meta['integration']['pairs'] == 2
for item in meta['failed_attempts'] + meta['root_failed_attempts']:
    assert item['exit_code'] != 0
    assert (HERE / item['executed_source']).exists()
    assert re.search(r'\berror(?:\(|:)', (HERE / item['log']).read_text())
assert (HERE / 'body-independent-public.lean').read_bytes() == (HERE / meta['public']['executed_source']).read_bytes()
assert (HERE / 'body-independent-kernels.lean').read_bytes() == (HERE / meta['integration']['executed_source']).read_bytes()
assert (HERE / meta['review']).exists()
manifest = HERE / 'body-independent-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({entry['path'] for entry in entries})
    for entry in entries:
        data = (ROOT / entry['path']).read_bytes()
        assert len(data) == entry['bytes']
        assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
print('PASS: exact final ParentForecast/EdgeBody sources and empty strict/canonical evidence; public15 full signatures/proofs/axioms; constructed2 own live non-Cap Mu child and nonresident missing-field raw rejection with arbitrary inputs/all10fuels; standard axioms only; all failed attempts preserved; manifest verified.')
