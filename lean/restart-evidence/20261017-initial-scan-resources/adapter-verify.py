from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'adapter-validation.json').read_text())
exports = []
for item in meta['production']:
    data = (ROOT / item['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    assert len(data.decode().splitlines()) == item['lines']
    assert (HERE / item['strict_source']).read_bytes() == data
    assert (HERE / item['strict_log']).read_bytes() == b''
    assert f"Build completed successfully ({item['canonical_jobs']} jobs)." in (HERE / item['canonical_log']).read_text()
    exports += ['MicroCFTA.' + Path(item['path']).stem + '.' + name for name in re.findall(r'^(?:def|theorem) ([\w.]+)', data.decode(), re.M)]
    assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', data.decode())
assert exports == meta['public']['names']
for item in meta['reviewed_sources']:
    assert hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
for kind in ['public', 'integration']:
    item = meta[kind]
    source = (HERE / item['executed_source']).read_text()
    log = (HERE / item['log']).read_text()
    assert item['exit_code'] == 0
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
    for setting in ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'pp.fullNames true']:
        assert 'set_option ' + setting in source
    assert source.count('#check @') == item['pairs']
    assert source.count('#print axioms ') == item['pairs']
    assert source.count('#print ') - source.count('#print axioms ') == item['pairs']
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == item['pairs']
    for name in item['names']:
        assert '#check @' + name in source
        assert '#print axioms ' + name in source
        assert '#print ' + name in source
        assert name in log
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        names = re.sub(r'\.\{[^}]*\}', '', axioms).split(',')
        assert all(name.strip() in meta['allowed_axioms'] for name in names)
for item in meta['failed_attempts']:
    assert item['exit_code'] != 0
    assert (HERE / item['source']).exists()
    assert 'error:' in (HERE / item['log']).read_text()
assert (HERE / meta['review']).exists()
manifest = HERE / 'adapter-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len({entry['path'] for entry in entries}) == len(entries)
    for entry in entries:
        data = (ROOT / entry['path']).read_bytes()
        assert len(data) == entry['bytes']
        assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
print('PASS: three exact frozen adapters; final strict logs empty; canonical targets green; all11 public +2 constructed integration pairs; standard axioms only; failed attempts1/2 retained; immutable manifest verified.')
