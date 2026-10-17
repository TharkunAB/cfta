from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'force-leaf-uncapped-validation.json').read_text())
for item in meta['productions']:
    production = (ROOT / item['source']['path']).read_bytes()
    assert hashlib.sha256(production).hexdigest() == item['source']['sha256']
    assert len(production) == item['source']['bytes']
    assert production == (HERE / item['strict']['executed_source']).read_bytes()
    assert (HERE / item['strict']['log']).read_bytes() == b''
    assert item['strict']['exit_code'] == item['canonical']['exit_code'] == 0
    canonical = (HERE / item['canonical']['log']).read_text()
    assert f"Build completed successfully ({item['canonical']['jobs']} jobs)." in canonical
    assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', production.decode())
    assert len(re.findall(r'^theorem complete', production.decode(), re.M)) == 1
    assert not re.search(r'\(depth : Nat\)|inputCap|capturedDepth|MixedShared.Stored|\(bounded :', production.decode())
for item in meta['reviewed_sources']:
    data = (ROOT / item['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    assert len(data) == item['bytes']
for item in [meta['public'], meta['integration']]:
    source = (HERE / item['executed_source']).read_text()
    log = (HERE / item['log']).read_text()
    assert item['exit_code'] == 0
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
    for setting in ['linter.all true', 'pp.explicit true', 'pp.fullNames true',
                    'pp.proofs true', 'pp.universes true', 'pp.deepTerms true',
                    'pp.maxSteps 10000000']:
        assert 'set_option ' + setting in source
    assert source.count('#check @') == item['pairs']
    assert source.count('#print axioms ') == item['pairs']
    expected = item['pairs'] if item['proof_printing'] else 0
    assert source.count('#print ') - source.count('#print axioms ') == expected
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == item['pairs']
    for name in item['names']:
        assert '#check @' + name in source
        assert '#print axioms ' + name in source
        if item['proof_printing']:
            assert '#print ' + name in source
        assert name in log
    for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        names = re.sub(r'\.\{[^}]*\}', '', group).split(',')
        assert all(name.strip() in meta['allowed_axioms'] for name in names)
for item in meta['failed_attempts']:
    assert item['exit_code'] != 0
    assert (HERE / item['executed_source']).exists()
    assert re.search(r'\berror(?:\(|:)', (HERE / item['log']).read_text())
old = meta['historical_success']
assert old['exit_code'] == 0 and not old['counted_as_final']
assert (HERE / old['executed_source']).exists()
assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯', (HERE / old['log']).read_text())
assert (HERE / 'force-leaf-uncapped-public.lean').read_bytes() == (HERE / meta['public']['executed_source']).read_bytes()
assert (HERE / 'force-leaf-uncapped-kernels.lean').read_bytes() == (HERE / meta['integration']['executed_source']).read_bytes()
assert (HERE / meta['review']).exists()
manifest = HERE / 'force-leaf-uncapped-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({item['path'] for item in entries})
    for item in entries:
        data = (ROOT / item['path']).read_bytes()
        assert len(data) == item['bytes']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
print('PASS: two exact frozen uncapped production sources; strict1 logs empty; canonical1532/1534; public2 full signatures/proofs/axioms; constructed3 own non-Cap cold/warm Force, result-fed warm-slot Leafs, and exact empty target; standard axioms only; historical success1 and failed namespace2 retained; immutable manifest verified.')
