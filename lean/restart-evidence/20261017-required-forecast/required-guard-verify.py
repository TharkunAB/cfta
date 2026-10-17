"""Verify pinned Required contracts and immutable initial-only integration checks."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / 'required-guard-manifest.json').read_text())
for item in manifest['entries']:
    actual = hashlib.sha256((root / item['path']).read_bytes()).hexdigest()
    assert actual == item['sha256'], (item['path'], actual)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for prefix, attempt, expected in [('required-guard-public', 1, 2), ('required-guard-kernels', 7, 2)]:
    source = (evidence / f'{prefix}-{attempt}.source.lean').read_text()
    log = (evidence / f'{prefix}-{attempt}.log').read_text()
    assert len(re.findall(r'^#check @', source, re.M)) == expected
    assert len(re.findall(r'^#print axioms ', source, re.M)) == expected
    assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.', log)
    for option in ['pp.explicit', 'pp.fullNames', 'pp.proofs', 'pp.universes', 'pp.deepTerms']:
        assert f'set_option {option} true' in source
    blocks = re.findall(r'depends on axioms: \[([^\]]*)\]', log, re.S)
    assert len(blocks) + log.count('does not depend on any axioms') == expected
    for block in blocks:
        names = {re.sub(r'\.\{[^}]+\}', '', n.strip()) for n in block.split(',') if n.strip()}
        assert names <= allowed, names
assert (evidence / 'required-guard-kernels-4.log').stat().st_size == 0
for attempt in [1, 2, 3, 5, 6]:
    log = (evidence / f'required-guard-kernels-{attempt}.log').read_text()
    assert re.search(r'error(?:\(|:)', log), attempt
for attempt in range(1, 8):
    for suffix in ['source.lean', 'log']:
        assert (evidence / f'required-guard-kernels-{attempt}.{suffix}').is_file()
index = json.loads((evidence / 'required-guard-source-index.json').read_text())
assert len(index['source_paths']) == 18 and index['lean_headers'] == 59
assert (evidence / 'required-guard-headers.md').read_text().count('```lean') == 59
for filename in ['worker-numeric-canonical-1.log', 'worker-initial-canonical-1.log',
                 'open-read-canonical-1.log', 'required-forecast-canonical-2.log']:
    assert 'Build completed successfully' in (evidence / filename).read_text()
print(f'PASS: {len(manifest["entries"])} hashes; public 2 and initial-only kernel 2 pairs; standard axioms; 18 source files and 59 headers; all seven immutable attempts retained')
