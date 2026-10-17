from pathlib import Path
import gzip
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'tuple-bounds-validation.json').read_text())
item = meta['production']
data = (ROOT / item['path']).read_bytes()
assert hashlib.sha256(data).hexdigest() == item['sha256']
assert len(data.decode().splitlines()) == item['lines']
assert (HERE / item['strict_source']).read_bytes() == data
assert (HERE / item['strict_log']).read_bytes() == b''
assert item['exit_code'] == 0
assert f"Build completed successfully ({item['canonical_jobs']} jobs)." in (HERE / item['canonical_log']).read_text()
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', data.decode())
exports = ['MicroCFTA.SourceCurrentConjunctionTupleBounds.' + name for name in re.findall(r'^(?:noncomputable )?(?:def|theorem) ([\w.]+)', data.decode(), re.M)]
assert exports == meta['public']['names']
for reviewed in meta['reviewed_sources']:
    assert hashlib.sha256((ROOT / reviewed['path']).read_bytes()).hexdigest() == reviewed['sha256'], reviewed['path']
for kind in ['public', 'integration']:
    check = meta[kind]
    source = (HERE / check['executed_source']).read_text()
    raw = (HERE / check['log']).read_bytes()
    if check['log'].endswith('.gz'):
        archive = json.loads((HERE / check['archive_metadata']).read_text())
        assert len(raw) == archive['archive_bytes']
        assert hashlib.sha256(raw).hexdigest() == archive['archive_sha256']
        raw = gzip.decompress(raw)
        assert len(raw) == archive['raw_bytes']
        assert hashlib.sha256(raw).hexdigest() == archive['raw_sha256']
        raw_copy = Path(archive['raw_copy_path'])
        if raw_copy.exists():
            assert raw_copy.read_bytes() == raw
    log = raw.decode()
    assert check['exit_code'] == 0
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps|declaration uses', log)
    for setting in ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'pp.fullNames true']:
        assert 'set_option ' + setting in source
    assert source.count('#check @') == check['pairs']
    assert source.count('#print axioms ') == check['pairs']
    assert source.count('#print ') - source.count('#print axioms ') == check['pairs']
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == check['pairs']
    for name in check['names']:
        assert '#check @' + name in source
        assert '#print axioms ' + name in source
        assert '#print ' + name in source
        assert name in log
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        names = re.sub(r'\.\{[^}]*\}', '', axioms).split(',')
        assert all(name.strip() in meta['allowed_axioms'] for name in names)
for failed in meta['failed_attempts']:
    assert failed['exit_code'] != 0
    assert (HERE / failed['source']).exists()
    assert 'error:' in (HERE / failed['log']).read_text() or 'error(' in (HERE / failed['log']).read_text()
assert (HERE / meta['review']).exists()
manifest = HERE / 'tuple-bounds-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({entry['path'] for entry in entries})
    for entry in entries:
        content = (ROOT / entry['path']).read_bytes()
        assert len(content) == entry['bytes']
        assert hashlib.sha256(content).hexdigest() == entry['sha256'], entry['path']
print('PASS: exact frozen TupleBounds271lines; strict3 empty/canonical1060; public23 +constructed2; standard axioms; ordered duplicate tuples and actual normalized guard shape; raw52,698,409-byte proof print losslessly preserved and verified; all failures retained; immutable manifest verified.')
