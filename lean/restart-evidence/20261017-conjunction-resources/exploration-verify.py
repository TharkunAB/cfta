from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'exploration-validation.json').read_text())
exports = []
for item in meta['production']:
    data = (ROOT / item['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    assert len(data.decode().splitlines()) == item['lines']
    assert (HERE / item['strict_source']).read_bytes() == data
    assert (HERE / item['strict_log']).read_bytes() == b''
    assert f"Build completed successfully ({item['canonical_jobs']} jobs)." in (HERE / item['canonical_log']).read_text()
    assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', data.decode())
    exports += ['MicroCFTA.' + Path(item['path']).stem + '.' + name for name in re.findall(r'^(?:noncomputable )?(?:def|theorem) ([\w.]+)', data.decode(), re.M)]
assert exports == meta['public']['names']
for item in meta['reviewed_sources']:
    assert hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
for item in [meta['public']] + meta['integrations']:
    source = (HERE / item['executed_source']).read_text()
    log = (HERE / item['log']).read_text()
    assert item['exit_code'] == 0
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
    for setting in ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'pp.fullNames true']:
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
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        names = re.sub(r'\.\{[^}]*\}', '', axioms).split(',')
        assert all(name.strip() in meta['allowed_axioms'] for name in names)
old = meta['historical_public']
old_source = (HERE / old['executed_source']).read_text()
old_log = (HERE / old['log']).read_text()
assert old['exit_code'] == 0
assert old_source.count('#print axioms ') == old['pairs']
assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx', old_log)
for item in meta['failed_attempts']:
    assert item['exit_code'] != 0
    assert (HERE / item['source']).exists()
    log = (HERE / item['log']).read_text()
    assert 'error:' in log or 'error(' in log
assert (HERE / meta['review']).exists()
manifest = HERE / 'exploration-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({entry['path'] for entry in entries})
    for entry in entries:
        content = (ROOT / entry['path']).read_bytes()
        assert len(content) == entry['bytes']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], entry['path']
print('PASS: three exact frozen Rows/Worklist/Numeric sources; final strict logs empty/canonical1265+1296+1300; all27 public +3 initial constructed integrations; standard axioms; open skipped pending and same full memo worker preserved; no production edits; failed attempts retained; immutable manifest verified.')
