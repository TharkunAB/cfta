#!/usr/bin/env python3
"""Verify the frozen read-only publication bare-self review."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'independent-bare-review-manifest.json').read_text())


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


for entry in manifest['entries']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], entry['path']
    assert sha(path) == entry['sha256'], entry['path']
for stem in manifest['reviewed_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'][-1] == str(source), stem
        assert '-Dlinter.all=true' in meta['command'], stem
assert not (HERE / 'publication-bare-direct-2.log').read_bytes()
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentPublicationBareParity.lean') == sha(HERE / 'publication-bare-direct-2.source.lean')
canonical = (HERE / 'publication-bare-canonical-1.log').read_text()
assert 'Build completed successfully (274 jobs).' in canonical
assert not re.search(r'warning:|error:|failed to pretty print', canonical)
source = (HERE / 'publication-bare-public-1.source.lean').read_text()
log = (HERE / 'publication-bare-public-1.log').read_text()
for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
               'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
    assert 'set_option ' + option in source, option
for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
    assert len(re.findall(pattern, source, re.M)) == 1, pattern
assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|truncated)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.', log)
reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
assert len(reports) + len(re.findall('does not depend on any axioms', log)) == 1
for report in reports:
    clean = re.sub(r'\.\{[^}]*\}', '', report)
    assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
                  'existing_public_pairs_reviewed': 1, 'constructed_pairs_reviewed': 0,
                  'new_pairs': 0, 'builds_repeated': 0}))
