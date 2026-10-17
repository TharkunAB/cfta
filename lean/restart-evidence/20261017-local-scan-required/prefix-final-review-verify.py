from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'prefix-final-review-source-pins.json').read_text())
production = (ROOT / meta['production']['path']).read_bytes()
assert hashlib.sha256(production).hexdigest() == meta['production']['sha256']
assert len(production) == meta['production']['bytes']
assert production == (HERE / meta['strict']['executed_source']).read_bytes()
assert (HERE / meta['strict']['log']).read_bytes() == b''
assert meta['strict']['exit_code'] == 0
canonical = (HERE / meta['canonical']['log']).read_text()
assert 'Built MicroCFTA.SourceCurrentScanRequiredNumeric' in canonical
assert f"Build completed successfully ({meta['canonical']['jobs']} jobs)." in canonical
assert meta['canonical']['exit_code'] == 0
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', production.decode())
for item in meta['reviewed_sources']:
    data = (ROOT / item['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    assert len(data) == item['bytes']
item = meta['public']
source = (HERE / item['executed_source']).read_text()
log = (HERE / item['log']).read_text()
assert item['exit_code'] == 0
assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
for setting in ['linter.all true', 'pp.explicit true', 'pp.fullNames true',
                'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
                'pp.maxSteps 10000000']:
    assert 'set_option ' + setting in source
assert item['pairs'] == len(item['names']) == len(set(item['names'])) == 22
assert source.count('#check @') == item['pairs']
assert source.count('#print axioms ') == item['pairs']
assert source.count('#print ') - source.count('#print axioms ') == item['pairs']
assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == item['pairs']
for name in item['names']:
    assert '#check @' + name in source
    assert '#print axioms ' + name in source
    assert '#print ' + name in source
    assert name in log
heads = re.findall(r'^(?:inductive|structure|theorem) (\w+)', production.decode(), re.M)
assert heads == ['Execution', 'Reads', 'Receipt', 'complete']
fields = ['actual','reads','frame','fits','post','originals','available','length','selected','domains','rejected','language','ranges','run']
for name in heads + ['Execution.stopped','Execution.prepared','Reads.stopped','Reads.prepared'] + ['Receipt.' + x for x in fields]:
    assert 'MicroCFTA.SourceCurrentScanRequiredNumeric.' + name in item['names']
for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
    axioms = re.sub(r'\.\{[^}]*\}', '', group).split(',')
    assert all(name.strip() in meta['allowed_axioms'] for name in axioms)
assert (HERE / 'prefix-final-review-public.lean').read_bytes() == (HERE / item['executed_source']).read_bytes()
old = meta['historical_probe']
assert old['exit_code'] == 0 and not old['counted_as_final']
assert (HERE / old['log']).read_text().count('⋯') == old['format_omissions'] == 1
assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx', (HERE / old['log']).read_text())
assert (HERE / old['executed_source']).exists()
assert (HERE / meta['review']).exists()
manifest = HERE / 'prefix-final-review-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({item['path'] for item in entries})
    for entry in entries:
        data = (ROOT / entry['path']).read_bytes()
        assert len(data) == entry['bytes']
        assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
print('PASS: final root source24534bc6; strict4 empty/canonical1716; exact final source pins; all22 handwritten/projection/constructor heads with full signatures/proofs and standard axioms; no omissions/diagnostics; earlier formatting pass retained; read-only semantic review and immutable manifest verified.')
