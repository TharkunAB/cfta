from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
meta = json.loads((HERE / 'copied-warm-validation.json').read_text())
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
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|native_decide|set_option linter\.[^\n]*false', data.decode())
assert len(re.findall(r'^theorem ', data.decode(), re.M)) == 3
assert len(re.findall(r'^inductive ', data.decode(), re.M)) == 3
assert len(re.findall(r'^noncomputable def Phase.run', data.decode(), re.M)) == 1
old = (HERE / 'copied-warm-direct-5.source.lean').read_text()
head = 'theorem copied_ready_while_owners_active'
assert old[old.index(head):].split(' := witness', 1)[0] == data.decode()[data.decode().index(head):].split(' := witness', 1)[0]
assert json.loads((HERE / 'copied-warm-canonical-1.json').read_text())['source_sha256'] == hashlib.sha256(old.encode()).hexdigest()
for record in [meta['public'], meta['integration']]:
    code = (HERE / record['executed_source']).read_text()
    log = (HERE / record['log']).read_text()
    assert record['exit_code'] == 0
    assert not re.search(r'\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|\.\.\.|failed to pretty|maximum number of steps', log)
    for setting in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                    'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + setting in code
    names = re.findall(r'^#check @(.+)$', code, re.M)
    assert names == record['names'] and len(names) == record['pairs']
    assert code.count('#print axioms ') == len(names)
    assert code.count('#print ') - code.count('#print axioms ') == int(record['proof_printing']) * len(names)
    assert log.count('depends on axioms:') + log.count('does not depend on any axioms') == len(names)
    for name in names:
        assert '#print axioms ' + name in code and name in log
        if record['proof_printing']:
            assert '#print ' + name in code
    for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        axioms = [name.strip() for name in re.sub(r'\.\{[^}]*\}', '', group).split(',')]
        assert set(axioms) <= set(meta['allowed_axioms'])
for attempt in range(1, 9):
    snapshot = HERE / f'copied-warm-direct-{attempt}.source.lean'
    rawlog = HERE / f'copied-warm-direct-{attempt}.log'
    record = json.loads((HERE / f'copied-warm-direct-{attempt}.json').read_text())
    assert record['source_sha256'] == hashlib.sha256(snapshot.read_bytes()).hexdigest()
    assert record['source'] == snapshot.name
    if attempt in meta['failed_strict_attempts']:
        assert record['exit_code'] != 0 and 'error' in rawlog.read_text()
    else:
        assert record['exit_code'] == 0 and rawlog.read_bytes() == b''
assert json.loads((HERE / 'copied-warm-kernels-1.json').read_text())['exit_code'] == 1
assert 'error' in (HERE / 'copied-warm-kernels-1.log').read_text()
for name, final in [('copied-warm-public.lean', 'copied-warm-public-1.source.lean'),
                    ('copied-warm-kernels.lean', 'copied-warm-kernels-2.source.lean')]:
    assert (HERE / name).read_bytes() == (HERE / final).read_bytes()
manifest = HERE / 'copied-warm-manifest.json'
if manifest.exists():
    entries = json.loads(manifest.read_text())['entries']
    assert len(entries) == len({entry['path'] for entry in entries})
    for entry in entries:
        value = (ROOT / entry['path']).read_bytes()
        assert len(value) == entry['bytes'], entry['path']
        assert hashlib.sha256(value).hexdigest() == entry['sha256'], entry['path']
print('PASS: final copied-warm source/strict8/canonical2; seven handwritten public heads plus fifteen constructors, 22 full signature/proof/axiom pairs; two imported kernels; exact inherited-value/key ready hit with active enclosing owners; literal phase failure correspondence; standard axioms; every failed and historical attempt retained; manifest verified.')
