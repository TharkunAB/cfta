"""Verify immutable initial Required numeric integration evidence."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / 'guard-numeric-manifest.json').read_text())
for item in manifest['entries']:
    actual = hashlib.sha256((root / item['path']).read_bytes()).hexdigest()
    assert actual == item['sha256'], (item['path'], actual)
assert (evidence / 'guard-numeric-fixture-1.log').stat().st_size == 0
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for prefix in ['guard-numeric-public', 'guard-numeric-kernels']:
    source = (evidence / f'{prefix}-1.source.lean').read_text()
    log = (evidence / f'{prefix}-1.log').read_text()
    assert len(re.findall(r'^#check @', source, re.M)) == 2
    assert len(re.findall(r'^#print axioms ', source, re.M)) == 2
    assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.', log)
    for name in ['pp.explicit', 'pp.fullNames', 'pp.proofs', 'pp.universes', 'pp.deepTerms']:
        assert f'set_option {name} true' in source
    blocks = re.findall(r'depends on axioms: \[([^\]]*)\]', log, re.S)
    assert len(blocks) + log.count('does not depend on any axioms') == 2
    for block in blocks:
        names = {re.sub(r'\.\{[^}]+\}', '', n.strip()) for n in block.split(',') if n.strip()}
        assert names <= allowed, names
source = (evidence / 'guard-numeric-kernels-1.source.lean').read_text()
assert source.count('SourceCurrentConstrainedCapRequiredInitialNumeric.caller ') == 2
assert 'QueryFits requiredProfile' in source and 'QueryFits emptyProfile' in source
assert 'QueryFits' in source and 'requiredReader ≤ reader' in source
index = json.loads((evidence / 'guard-numeric-source-index.json').read_text())
assert len(index['source_paths']) == 15 and index['lean_headers'] == 40
assert (evidence / 'guard-numeric-headers.md').read_text().count('```lean') == 40
assert 'Build completed successfully' in (evidence / 'initial-canonical-1.log').read_text()
print(f'PASS: {len(manifest["entries"])} hashes; two public and two initial-only computed integration pairs; standard axioms; strict-empty fixture; 15 source files and 40 exact headers')
