#!/usr/bin/env python3
"""Verify the read-only retained-writer review pins without running Lean."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
MANIFEST = HERE / 'independent-retained-writer-review-manifest.json'
manifest = json.loads(MANIFEST.read_text())


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


for entry in manifest['entries']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], entry['path']
    assert sha(path) == entry['sha256'], entry['path']
source = ROOT / manifest['production']
assert sha(source) == manifest['source_sha256']
assert source.read_bytes() == (HERE / 'retained-writer-direct-5.source.lean').read_bytes()
old = (HERE / 'retained-writer-direct-4.source.lean').read_text()
assert old.replace(',Option.getD_some', '') == source.read_text()
assert 'warning: This simp argument is unused' in (HERE / 'retained-writer-direct-4.log').read_text()
for stem in ['retained-writer-direct-5', 'retained-writer-kernels-3']:
    assert (HERE / (stem + '.log')).stat().st_size == 0, stem
canonical = (HERE / 'retained-writer-canonical-2.log').read_text()
assert 'Build completed successfully (630 jobs).' in canonical
assert not re.search(r'\b(?:warning|error)(?:\([^)]*\))?:', canonical)
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    if 'source' in meta:
        frozen = HERE / meta['source']
        assert sha(frozen) == meta['sha256'], stem
        assert meta['command'][-1] == str(frozen), stem
        assert '-Dlinter.all=true' in meta['command'], stem
for stem, count in [('retained-writer-public-2', 7), ('retained-writer-kernels-public-1', 2)]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    frozen = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in frozen, (stem, option)
    assert len(re.findall(r'^#check @', frozen, re.M)) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', frozen, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', frozen, re.M)) == count, stem
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|truncated)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall('does not depend on any axioms', log)) == count
    for report in reports:
        clean = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
printed = (HERE / 'retained-writer-kernels-public-1.source.lean').read_text()
printer_free = re.sub(r'^set_option pp\.[^\n]*\n', '', printed, flags=re.M)
assert printer_free.startswith((HERE / 'retained-writer-kernels-3.source.lean').read_text())
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
                  'reviewed_public_pairs': 7, 'reviewed_constructed_pairs': 2,
                  'additional_pairs': 0, 'review_builds': 0, 'source_sha256': manifest['source_sha256']}))
