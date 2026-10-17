from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'edge-idle-manifest.json').read_text())
entries = manifest['entries']
assert len(entries) == len({entry['path'] for entry in entries})
for entry in entries:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
production = ROOT / 'lean/MicroCFTA/SourceCurrentOuterEdgeIdle.lean'
assert hashlib.sha256(production.read_bytes()).hexdigest() == '4ced480a88de5e01db05579b1019635626d5c7207d626b3d1cadc31357032ba5'
assert production.read_bytes() == (HERE / 'edge-idle-direct-4.source.lean').read_bytes()
assert (HERE / 'edge-idle-direct-4.log').read_bytes() == b''
assert (HERE / 'edge-idle-kernel-strict-1.log').read_bytes() == b''
canonical = (HERE / 'edge-idle-canonical-1.log').read_text()
assert canonical.startswith('4294967296\n4294967296\n0\n')
assert 'Build completed successfully (1413 jobs).' in canonical
assert 'error:' not in canonical
for attempt in (1, 2, 3):
    assert 'error:' in (HERE / f'edge-idle-direct-{attempt}.log').read_text()
assert 'error:' in (HERE / 'edge-idle-kernels-1.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for stem, count, proof_prints in [('edge-idle-public-1', 12, True), ('edge-idle-kernels-2', 3, False)]:
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
kernel = (HERE / 'edge-idle-kernels-2.source.lean').read_text()
stripped = '\n'.join(line for line in kernel.splitlines() if not line.startswith(('#check ', '#print '))) + '\n'
assert (HERE / 'edge-idle-kernel-strict-1.source.lean').read_text() == stripped
assert (HERE / 'edge-idle-kernels.lean').read_text() == kernel
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false', production.read_text())
print(f'PASS: {len(entries)} hashes; strict4 empty; canonical1413; public12; constructed3; standard axioms')
