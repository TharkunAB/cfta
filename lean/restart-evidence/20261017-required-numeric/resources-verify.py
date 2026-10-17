"""Verify exact Required primitive resource transfers and immutable attempts."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
p = Path(__file__).resolve().parent
m = json.loads((p / 'resources-manifest.json').read_text())
for item in m['entries']:
    assert hashlib.sha256((root / item['path']).read_bytes()).hexdigest() == item['sha256'], item
assert (p / 'resources-direct-3.log').stat().st_size == 0
assert (p / 'resources-direct-3.source.lean').read_bytes() == (root / 'lean/MicroCFTA/SourceCurrentConstrainedCapRequiredResources.lean').read_bytes()
assert 'Build completed successfully (1521 jobs)' in (p / 'resources-canonical-2.log').read_text()
s = (p / 'resources-public-1.source.lean').read_text()
l = (p / 'resources-public-1.log').read_text()
assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.', l)
assert len(re.findall(r'^#check @', s, re.M)) == len(re.findall(r'^#print axioms ', s, re.M)) == 12
blocks = re.findall(r'depends on axioms: \[([^\]]*)\]', l, re.S)
assert len(blocks) + l.count('does not depend on any axioms') == 12
for block in blocks:
    assert {re.sub(r'\.\{[^}]+\}', '', n.strip()) for n in block.split(',') if n.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}
print(f'PASS: {len(m["entries"])} hashes; 12 public full pairs; strict clean; canonical1521; all failed attempts preserved')
