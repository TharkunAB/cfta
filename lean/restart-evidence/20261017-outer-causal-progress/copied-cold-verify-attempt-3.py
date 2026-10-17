from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'copied-cold-validation.json').read_text())
source = (ROOT / meta['production']).read_bytes()
assert hashlib.sha256(source).hexdigest() == meta['source_sha256']
assert source == (HERE / 'copied-cold-direct-3.source.lean').read_bytes()
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|native_decide|set_option linter\.[^\n]*false', source.decode())
assert len(re.findall(r'^theorem ', source.decode(), re.M)) == 1
old = (HERE / 'copied-cold-direct-2.source.lean').read_text()
head = 'theorem copied_cold_while_owners_active :'
old_header, old_body = old[old.index(head):].split(' := by\n', 1)
old_body = old_body.split('\nend MicroCFTA.SourceCurrentOuterCopiedCold', 1)[0]
current = source.decode()
assert current[current.index(head):].split(' := witness', 1)[0] == old_header
new_body = current[current.index('private theorem witness :'):].split(' := by\n', 1)[1]
new_body = new_body.split('\n\n/-- Keep the public proof print', 1)[0]
assert old_body == new_body
assert 'theorem copied_cold_while_owners_active :' in source.decode()
assert '¬ SourceCurrentRequiredRowOrigins.Origin recursiveValue copiedOwner.value' in source.decode()
assert (HERE / 'copied-cold-direct-3.log').read_bytes() == b''
assert (HERE / 'copied-cold-kernels-strict-2.log').read_bytes() == b''

runs = sorted(path.stem for path in HERE.glob('copied-cold-*.json')
              if 'command' in json.loads(path.read_text()))
for stem in runs:
    record = json.loads((HERE / (stem + '.json')).read_text())
    limits = json.loads((HERE / record['limits']).read_text())
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    assert record['exit_code'] == meta['terminated_probe_attempts'].get(stem, 1 if stem in meta['failed_attempts'] else 0)
    assert record['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped'
    assert record['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
    if 'source' in record:
        snapshot = HERE / record['source']
        assert record['sha256'] == hashlib.sha256(snapshot.read_bytes()).hexdigest()
        assert record['command'][-1] == str(snapshot)
        assert record['command'][-2] == '-Dlinter.all=true'
    if stem in meta['failed_attempts']:
        assert 'error:' in (HERE / record['log']).read_text()

assert 'failed to pretty print expression' in (HERE / 'copied-cold-public-1.log').read_text()

canonical = (HERE / 'copied-cold-canonical-2.log').read_text()
assert f"Build completed successfully ({meta['canonical_jobs']} jobs)." in canonical
assert len(re.findall(r'^warning:', canonical, re.M)) == 1
assert 'warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:' in canonical
assert 'error:' not in canonical
assert 'warning: MicroCFTA/SourceCurrentOuterCopiedCold' not in canonical

options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
           'pp.maxSteps 10000000']
for group in meta['groups']:
    stem = group['stem']
    code = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    for option in options:
        assert 'set_option ' + option in code
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|\.\.\.|failed to pretty|maximum number of steps', log)
    assert re.findall(r'^#check @(.+)$', code, re.M) == group['names']
    assert code.count('#print axioms ') == group['pairs']
    assert code.count('#print ') - code.count('#print axioms ') == int(group['full_proof']) * group['pairs']
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == group['pairs']
    for name in group['names']:
        assert name in log and '#print axioms ' + name in code
    for names in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        assert set(name.strip() for name in names.split(',')) <= set(meta['allowed_axioms'])

for live, snapshot in [('copied-cold-public.lean', 'copied-cold-public-4.source.lean'),
                       ('copied-cold-kernels.lean', 'copied-cold-kernels-2.source.lean'),
                       ('copied-cold-kernels-strict.lean', 'copied-cold-kernels-strict-2.source.lean')]:
    assert (HERE / live).read_bytes() == (HERE / snapshot).read_bytes()
manifest = json.loads((HERE / 'copied-cold-manifest.json').read_text())
entries = manifest['entries']
assert len(entries) == len({entry['path'] for entry in entries})
for entry in entries:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
print(f'PASS: {len(entries)} frozen entries; strict3 and imported strict empty; canonical1776; public4 full proof and constructed2 standard axioms; effective4G/4G/swap0; cold reached copy plus own completed root and retained all-fuel warm hit; failed attempt retained.')
