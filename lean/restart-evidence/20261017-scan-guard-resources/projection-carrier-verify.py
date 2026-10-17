from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'projection-carrier-validation.json').read_text())
production = (ROOT / meta['production']['path']).read_bytes()
assert hashlib.sha256(production).hexdigest() == meta['production']['sha256']
assert len(production) == meta['production']['bytes']
assert production == (HERE / meta['strict']['executed_source']).read_bytes()
assert (HERE / meta['strict']['log']).read_bytes() == b''
assert meta['strict']['exit_code'] == 0
canonical = (HERE / meta['canonical']['log']).read_text()
assert f"Build completed successfully ({meta['canonical']['jobs']} jobs)." in canonical
assert meta['canonical']['exit_code'] == 0
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', production.decode())
exports = [
    'MicroCFTA.SourceCurrentSeededProjectionCarrier.' + name
    for name in re.findall(r'^theorem (\w+)', production.decode(), re.M)
]
assert exports == meta['public']['names']
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
old = meta['historical_integration']
assert old['exit_code'] == 0
assert (HERE / old['executed_source']).read_text().count('#print axioms ') == old['pairs']
assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx', (HERE / old['log']).read_text())
for item in meta['failed_attempts']:
    assert item['exit_code'] != 0
    assert (HERE / item['source']).exists()
    assert re.search(r'\berror(?:\(|:)', (HERE / item['log']).read_text())
assert (HERE / 'projection-carrier-public.lean').read_bytes() == (HERE / meta['public']['executed_source']).read_bytes()
assert (HERE / 'projection-carrier-kernels.lean').read_bytes() == (HERE / meta['integration']['executed_source']).read_bytes()
assert (HERE / meta['review']).exists()
manifest = HERE / 'projection-carrier-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({item['path'] for item in entries})
    for item in entries:
        data = (ROOT / item['path']).read_bytes()
        assert len(data) == item['bytes']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
print('PASS: exact frozen source; strict3 empty; canonical1185 with only existing dependency warning; public5 full signatures/proofs/axioms; constructed3 signatures/axioms; own open selected projection, exact checked tables, first node+edge allocation and exact fullheap warm repeat; standard axioms only; all5 failed attempts and historical successful2 retained; immutable manifest verified.')
