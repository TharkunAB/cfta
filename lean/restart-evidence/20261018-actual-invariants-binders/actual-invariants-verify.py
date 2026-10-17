#!/usr/bin/env python3
"""Verify the frozen operation-growth evidence without executing Lean."""
import hashlib
import json
import re
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'actual-invariants-manifest.json').read_text())
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
for entry in manifest['entries']:
    path = ROOT / entry['path']
    assert path.stat().st_size == entry['bytes'], str(path)
    assert sha(path) == entry['sha256'], str(path)
for path in HERE.glob('actual-invariants-*.json'):
    meta = json.loads(path.read_text())
    if not isinstance(meta, dict) or 'limits' not in meta:
        continue
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}, path.name
    assert (HERE / meta['log']).exists(), path.name
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], path.name
        assert meta['command'][-1] == str(source), path.name
        assert '-Dlinter.all=true' in meta['command'], path.name
for stem in manifest['selected_runs']:
    assert json.loads((HERE / (stem+'.json')).read_text())['exit_code'] == 0, stem
for stem in manifest['strict_empty']:
    assert (HERE / (stem+'.log')).stat().st_size == 0, stem
for production in manifest['productions']:
    assert sha(ROOT / production['path']) == production['sha256']
    assert sha(HERE / (production['strict']+'.source.lean')) == production['sha256']
for stem, jobs in manifest['canonical_jobs'].items():
    log = (HERE / (stem+'.log')).read_text()
    assert f'Build completed successfully ({jobs} jobs).' in log, stem
    assert 'error:' not in log, stem
    assert len(re.findall(r'^warning:', log, re.M)) == 1, stem
    assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in log, stem
for stem, count in manifest['probe_groups'].items():
    meta = json.loads((HERE / (stem+'.json')).read_text())
    source = (HERE / meta['source']).read_text()
    log = (HERE / meta['log']).read_text()
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true',
                   'pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|truncated)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|⋯|…|\.\.\.',log), stem
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
    assert len(reports)+len(re.findall('does not depend on any axioms',log)) == count, stem
    for report in reports:
        clean = re.sub(r'\.\{[^}]*\}', '',report)
        assert set(re.split(r',\s*',clean.strip())) <= {'propext','Classical.choice','Quot.sound'}, stem
assert (HERE/'actual-invariants-kernels-public-2.source.lean').read_bytes().startswith(
    (HERE/'actual-invariants-kernels-3.source.lean').read_bytes())
assert (HERE/'actual-invariants-kernels-2.log').stat().st_size == 282
print(json.dumps({'status':'PASS','entries':len(manifest['entries']),
    'public_pairs':17,'constructed_pairs':2,'strict_empty':True,
    'memory_max':4294967296,'memory_high':4294967296,'swap_max':0}))
