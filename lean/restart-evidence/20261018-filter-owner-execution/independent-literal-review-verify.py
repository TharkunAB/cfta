#!/usr/bin/env python3
"""Verify the independently reviewed frozen literal proof evidence."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'independent-literal-review-manifest.json').read_text())


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
for stem in ['literal-observations-direct-3', 'literal-congruence-direct-3', 'literal-congruence-kernels-1']:
    assert not (HERE / (stem + '.log')).read_bytes(), stem
for stem, jobs in [('literal-observations-canonical-1', 566), ('literal-congruence-canonical-1', 583)]:
    log = (HERE / (stem + '.log')).read_text()
    assert f'Build completed successfully ({jobs} jobs).' in log, stem
    assert not re.search(r'warning:|error:|failed to pretty print', log), stem
for stem, count in [('literal-observations-public-1', 2), ('literal-congruence-public-1', 2),
                    ('literal-congruence-kernels-public-1', 1)]:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in source, (stem, option)
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, source, re.M)) == count, (stem, pattern)
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|truncated)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall('does not depend on any axioms', log)) == count, stem
    for report in reports:
        clean = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem
for production, strict in [('SourceCurrentLiteralPartsObservations', 'literal-observations-direct-3'),
                           ('SourceCurrentStoredLiteralCongruence', 'literal-congruence-direct-3')]:
    assert sha(ROOT / 'lean/MicroCFTA' / (production + '.lean')) == sha(HERE / (strict + '.source.lean'))
fixture = (HERE / 'literal-congruence-kernels-1.source.lean').read_bytes()
public = (HERE / 'literal-congruence-kernels-public-1.source.lean').read_bytes()
assert public.startswith(fixture)
print(json.dumps({'status': 'PASS', 'entries': len(manifest['entries']),
                  'existing_public_pairs_reviewed': 4, 'existing_constructed_pairs_reviewed': 1,
                  'new_pairs': 0, 'builds_repeated': 0}))
