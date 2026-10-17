#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'class-phase-lineage-manifest.json').read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296',
        'memory.swap.max': '0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(source)], stem

for stem in ['class-phase-lineage-direct-1', 'class-phase-lineage-kernels-1']:
    assert not (HERE / (stem + '.log')).read_bytes(), stem
assert sha(ROOT / manifest['production']) == manifest['source_sha256']
assert sha(HERE / 'class-phase-lineage-direct-1.source.lean') == manifest['source_sha256']
assert 'Build completed successfully (1407 jobs).' in (HERE / 'class-phase-lineage-canonical-1.log').read_text()
for stem, count in [('class-phase-lineage-public-1', 2), ('class-phase-lineage-kernels-public-1', 1)]:
    source = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    for option in [
        'linter.all true', 'pp.explicit true', 'pp.fullNames true',
        'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
        'pp.deepTerms true', 'pp.maxSteps 10000000',
    ]:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    assert not re.search(
        r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|'
        r'uncaught exception|internal exception|maximum recursion depth|maximum number of heartbeats)'
        r'|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|pp\.rawOnError|⋯|…|\.\.\.', log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) + len(re.findall('does not depend on any axioms', log)) == count, stem
    for report in reports:
        clean = re.sub(r'\.\{[^}]*\}', '', report)
        assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, stem
for stem in ['public', 'kernels', 'kernels-public']:
    assert sha(HERE / ('class-phase-lineage-' + stem + '.lean')) == sha(
        HERE / ('class-phase-lineage-' + stem + '-1.source.lean'))
print(json.dumps({
    'status': 'PASS', 'entries': len(manifest['entries']), 'public_pairs': 2,
    'constructed_pairs': 1, 'groups': 2, 'full_proof': True,
    'strict_empty': True, 'canonical_jobs': 1407,
    'source_sha256': manifest['source_sha256'],
    'actual_memory_max_high_bytes': 4294967296, 'actual_swap_max_bytes': 0,
}))
