#!/usr/bin/env python3
"""Verify the frozen writer-child source and proof receipts."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'writer-child-kernels-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
production = ROOT / manifest['production']
assert hashlib.sha256(production.read_bytes()).hexdigest() == manifest['source_sha256']
assert production.read_bytes() == (HERE / 'writer-child-direct-7.source.lean').read_bytes()
assert (HERE / 'writer-child-direct-7.log').read_bytes() == b''
assert len(re.findall(r'(?m)^theorem ', production.read_text())) == 5
assert not re.search(r'\b(sorry|admit|axiom)\b', production.read_text())
assert (HERE / 'writer-child-kernels.lean').read_bytes() == (HERE / 'writer-child-kernels-6.source.lean').read_bytes()
limits = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
for stem, expected in manifest['attempt_results'].items():
    report = json.loads((HERE / (stem + '.json')).read_text())
    assert report['exit_code'] == expected, stem
    assert json.loads((HERE / report['limits']).read_text()) == limits, stem
    assert report['wrapper'][0] == '/home/tritlo/Code/heavy-management/bin/capped', stem
    assert report['wrapper'][1:5] == ['--mem', '4G', '--time', '5m'], stem
    assert '/leanprover--lean4---v4.34.1/bin/' in report['command'][0], stem
    assert report['observed_at'] and (HERE / report['log']).is_file(), stem
    if 'source' in report:
        snapshot = HERE / report['source']
        assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == report['sha256'], stem
        assert report['command'][-1] == str(snapshot), stem
        assert report['command'][1] == '-Dlinter.all=true', stem
    else:
        assert report['command'][-2:] == ['build', 'MicroCFTA.SourceCurrentNativeWriterChildOrigins'], stem
for stem in manifest['selected_runs']:
    assert manifest['attempt_results'][stem] == 0, stem
canonical = (HERE / 'writer-child-canonical-2.log').read_text()
assert 'Build completed successfully (1169 jobs).' in canonical
assert not re.search(r'error:|sorryAx|failed to pretty', canonical, re.I)
for match in re.finditer(r'(?m)^warning:.*$', canonical):
    assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in match.group(0)
options = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
for group in manifest['groups']:
    stem = group['stem']
    report = json.loads((HERE / (stem + '.json')).read_text())
    probe = (HERE / report['source']).read_text()
    output = (HERE / report['log']).read_text()
    for option in options:
        assert 'set_option ' + option in probe, (stem, option)
    assert not re.search(r'error:|warning:|sorryAx|failed to pretty|maximum number of steps|⋯|\.\.\.', output, re.I), stem
    assert len(re.findall(r'(?m)^#check @', probe)) == group['pairs'], stem
    assert len(re.findall(r'(?m)^#print axioms ', probe)) == group['pairs'], stem
    assert len(re.findall(r'(?m)^#print (?!axioms )', probe)) == group['pairs'], stem
    for name in group['names']:
        assert '#check @' + name in probe, (stem, name)
        assert re.search(r'(?m)^#print ' + re.escape(name) + r'$', probe), name
        assert '#print axioms ' + name in probe, (stem, name)
        assert 'theorem ' + name + ' :' in output, (stem, name)
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[(.*?)\]", output, re.S)
        assert match, (stem, name)
        axioms = {re.sub(r'\.\{[^}]*\}', '', item.strip()) for item in match.group(1).split(',') if item.strip()}
        assert axioms <= set(manifest['allowed_axioms']), (stem, axioms)
    assert len(group['names']) == group['pairs']
assert manifest['public_pairs'] == 5 and manifest['constructed_pairs'] == 2
assert manifest['probe_groups'] == len(manifest['groups']) == 2
assert sum(group['pairs'] for group in manifest['groups']) == 7
kernel = (HERE / 'writer-child-kernels-6.source.lean').read_text()
assert 'warm_child advanced_history advance_good' in kernel
assert kernel.count('SourceCurrentNativeWriterChildOrigins.rows_child advanced_history') == 2
assert 'edgeAfter.native.machine.heap.edges.next < advanced.native.machine.heap.edges.next' in kernel
assert 'first.referenceOf = .node 0' in kernel and 'mu.referenceOf = .mu 3' in kernel
assert 'SourceCurrentOuterEdgeIdle.initial' in (HERE / 'row-progress-independent-review.md').read_text()
print(f"PASS: {len(manifest['entries'])} pinned entries; 5 public + 2 constructed pairs; 2 groups; exact immutable attempts and effective 4 GiB limits verified.")
