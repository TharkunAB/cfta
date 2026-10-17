from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'scan-numeric-validation.json').read_text())
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
heads = re.findall(r'^(?:structure|theorem) (\w+)', production.decode(), re.M)
assert heads == ['Receipt', 'complete']
fields = re.findall(r'^  (\w+) :', production.decode(), re.M)
assert fields == ['actual', 'ranges', 'frame', 'fits', 'carrier', 'effects', 'available', 'correct', 'retained', 'run']
assert meta['public']['names'] == ['MicroCFTA.SourceCurrentScanNumeric.Receipt'] + ['MicroCFTA.SourceCurrentScanNumeric.Receipt.' + field for field in fields] + ['MicroCFTA.SourceCurrentScanNumeric.complete']
assert meta['public']['handwritten_declarations'] == 2
assert meta['public']['generated_field_projections'] == 10
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
assert (HERE / old['log']).read_text().count('warning:') == old['warnings']
assert not re.search(r'\berror(?:\(|:)|sorryAx', (HERE / old['log']).read_text())
for item in meta['failed_attempts']:
    assert item['exit_code'] != 0
    assert (HERE / item['source']).exists()
    assert re.search(r'\berror(?:\(|:)', (HERE / item['log']).read_text())
assert (HERE / 'scan-numeric-public.lean').read_bytes() == (HERE / meta['public']['executed_source']).read_bytes()
assert (HERE / 'scan-numeric-kernels.lean').read_bytes() == (HERE / meta['integration']['executed_source']).read_bytes()
assert (HERE / meta['review']).exists()
manifest = HERE / 'scan-numeric-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({item['path'] for item in entries})
    for item in entries:
        data = (ROOT / item['path']).read_bytes()
        assert len(data) == item['bytes']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
print('PASS: exact ScanNumeric frozen source; strict4 empty; canonical1582 with only existing dependency warning; public12 full signatures/proofs/axioms (2 handwritten+10 projections); own initial selected/skipped/missing Scan integration; derived original universal Ranges+exact full receipt preserved; standard axioms; all failed/warning attempts retained; immutable manifest verified.')
