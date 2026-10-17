from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'outer-key-manifest.json').read_text())
entries = manifest['entries']
assert len(entries) == len({entry['path'] for entry in entries})
for entry in entries:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']

source = ROOT / 'lean/MicroCFTA/SourceCurrentOuterKeyIdentity.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '7245813dd69faff928fc51d2660e771faf49f1b288234d468d6fdf36aa8aea36'
assert source.read_bytes() == (HERE / 'outer-key-direct-3.source.lean').read_bytes()
assert (HERE / 'outer-key-direct-3.log').read_bytes() == b''
assert (HERE / 'outer-key-kernel-strict-1.log').read_bytes() == b''
canonical = (HERE / 'outer-key-canonical-1.log').read_text()
assert canonical.startswith('4294967296\n4294967296\n0\n')
assert 'Build completed successfully (1120 jobs).' in canonical
assert 'error:' not in canonical
assert 'No medium found' in (HERE / 'outer-key-direct-1.log').read_text()
assert 'Operation not permitted' in (HERE / 'outer-key-direct-2.log').read_text()
for attempt in (1, 2):
    assert 'error:' in (HERE / f'outer-key-kernels-{attempt}.log').read_text()

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for stem, count, proof_prints in [('outer-key-public-1', 4, True), ('outer-key-kernels-3', 2, False)]:
    code = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|⋯|…|\.{3}|truncat|failed to pretty', log), stem
    checks = re.findall(r'^#check @(\S+)', code, re.M)
    assert len(checks) == count
    assert re.findall(r'^#print axioms (\S+)', code, re.M) == checks
    assert re.findall(r'^#print (?!axioms )(\S+)', code, re.M) == (checks if proof_prints else [])
    for setting in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                    'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + setting in code
    blocks = re.findall(r'depends on axioms:\s*\[([^]]*)\]', log, re.S)
    assert len(blocks) + log.count('does not depend on any axioms') == count
    for block in blocks:
        observed = {re.sub(r'\.\{[^}]+\}', '', name.strip()) for name in block.split(',') if name.strip()}
        assert observed <= allowed, observed
    assert json.loads((HERE / (stem + '.json')).read_text())['exit_code'] == 0

kernel = (HERE / 'outer-key-kernels-3.source.lean').read_text()
stripped = '\n'.join(line for line in kernel.splitlines() if not line.startswith(('#check ', '#print '))) + '\n'
assert (HERE / 'outer-key-kernel-strict-1.source.lean').read_text() == stripped
assert (HERE / 'outer-key-kernels.lean').read_text() == kernel
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', source.read_text())
print(f'PASS: {len(entries)} hashes; strict3 empty; canonical1120; public4; constructed2; standard axioms')
