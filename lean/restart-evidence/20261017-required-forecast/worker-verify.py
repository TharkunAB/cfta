"""Verify original-trie worker bounds, exact signatures, and immutable attempts."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / 'worker-manifest.json').read_text())
for item in manifest['entries']:
    assert hashlib.sha256((root / item['path']).read_bytes()).hexdigest() == item['sha256'], item
for prefix, attempt in [('worker-numeric', 5), ('worker-initial', 1)]:
    assert (evidence / f'{prefix}-direct-{attempt}.log').stat().st_size == 0
    assert (evidence / f'{prefix}-direct-{attempt}.source.lean').read_bytes() == (root / 'lean/MicroCFTA' / ('SourceCurrentRequiredWorkerNumeric.lean' if prefix == 'worker-numeric' else 'SourceCurrentConstrainedCapSelectedRequiredWorker.lean')).read_bytes()
    assert 'Build completed successfully' in (evidence / f'{prefix}-canonical-1.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for prefix, count in [('worker-public', 6), ('worker-contract', 1)]:
    source = (evidence / f'{prefix}-1.source.lean').read_text()
    log = (evidence / f'{prefix}-1.log').read_text()
    assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.', log)
    assert len(re.findall(r'^#check @', source, re.M)) == count
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count
    blocks = re.findall(r'depends on axioms: \[([^\]]*)\]', log, re.S)
    assert len(blocks) + log.count('does not depend on any axioms') == count
    for block in blocks:
        assert {re.sub(r'\.\{[^}]+\}', '', n.strip()) for n in block.split(',') if n.strip()} <= allowed
print(f'PASS: {len(manifest["entries"])} hashes; six public pairs; initial contract pair; two strict-clean canonical modules; immutable failed attempts')
