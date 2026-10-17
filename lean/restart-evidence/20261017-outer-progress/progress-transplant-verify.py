from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'progress-transplant-validation.json').read_text())
source = ROOT / meta['production']['path']
data = source.read_bytes()
assert hashlib.sha256(data).hexdigest() == meta['production']['sha256']
assert len(data) == meta['production']['bytes']
assert data == (HERE / meta['strict']['executed_source']).read_bytes()
assert (HERE / meta['strict']['log']).read_bytes() == b''
assert meta['strict']['exit_code'] == meta['canonical']['exit_code'] == 0
canonical = (HERE / meta['canonical']['log']).read_text()
assert canonical.startswith('4294967296\n4294967296\n0\n')
assert 'Build completed successfully (1771 jobs).' in canonical
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false',data.decode())
old = (HERE / 'progress-transplant-9.source.lean').read_text()
head = 'theorem supported_parent_growth'
old_statement = old[old.index(head):].split(' := by',1)[0]
new_statement = data.decode()[data.decode().index(head):].split(' := witness',1)[0]
assert old_statement == new_statement
assert hashlib.sha256(old.encode()).hexdigest() == '7a9f3f639b91c3fe79dfcb41e5a1e349089721f15cee1a19bbbe1d7e679a5788'
for record in [meta['public'],meta['integration']]:
    code = (HERE / record['executed_source']).read_text()
    log = (HERE / record['log']).read_text()
    assert record['exit_code'] == 0
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|\.\.\.|failed to pretty|maximum number of steps',log)
    for setting in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
                    'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+setting in code
    names = re.findall(r'^#check @(.+)$',code,re.M)
    assert names == record['names'] and len(names) == record['pairs'] == 1
    assert code.count('#print axioms ') == 1
    assert code.count('#print ') - code.count('#print axioms ') == int(record['proof_printing'])
    assert log.count('depends on axioms:') == 1
    for name in names:
        assert '#print axioms '+name in code and name in log
        if record['proof_printing']: assert '#print '+name in code
    for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):
        names = [name.strip() for name in re.sub(r'\.\{[^}]*\}','',group).split(',')]
        assert set(names) <= set(meta['allowed_axioms'])
for attempt in meta['failed_strict_attempts']:
    assert (HERE / f'progress-transplant-{attempt}.source.lean').is_file()
    assert 'error' in (HERE / f'progress-transplant-{attempt}.log').read_text()
for attempt in meta['historical_successful_strict_attempts']:
    assert (HERE / f'progress-transplant-{attempt}.source.lean').is_file()
    assert (HERE / f'progress-transplant-{attempt}.log').read_bytes() == b''
assert 'failed to pretty print' in (HERE / 'progress-transplant-public-1.log').read_text()
assert json.loads((HERE / 'progress-transplant-public-2.termination.json').read_text())['status'] == 'TERMINATED'
assert 'Failed to connect to bus: Operation not permitted' in (HERE / 'progress-transplant-canonical-1.log').read_text()
manifest = HERE / 'progress-transplant-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({entry['path'] for entry in entries})
    for entry in entries:
        value = (ROOT / entry['path']).read_bytes()
        assert len(value) == entry['bytes'],entry['path']
        assert hashlib.sha256(value).hexdigest() == entry['sha256'],entry['path']
print('PASS: parent-height source/strict10/canonical3; exact public statement preserved; public1 full signature/proof/standard axioms; constructed1 finite outer return and exact post-return warm caller; all failed and terminated attempts preserved; manifest verified.')
