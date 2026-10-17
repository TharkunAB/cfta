#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
MANIFEST = HERE / 'shared-edit-row-kernels-manifest.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads(MANIFEST.read_text())
for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    source = HERE / meta['source']
    assert sha(source) == meta['sha256'], stem
    assert meta['command'] == [
        '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
        '-Dlinter.all=true', str(source)], stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296',
        'memory.swap.max': '0'}, stem
    for option in [
        'linter.all true', 'pp.explicit true', 'pp.fullNames true',
        'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
        'pp.deepTerms true', 'pp.maxSteps 10000000',
    ]:
        assert 'set_option ' + option in source.read_text(), (stem, option)

strict = 'shared-edit-row-kernels-7'
public = 'shared-edit-row-kernels-public-1'
assert not (HERE / (strict + '.log')).read_bytes()
assert sha(HERE / 'shared-edit-row-kernels.lean') == sha(HERE / (strict + '.source.lean'))
assert sha(HERE / 'shared-edit-row-kernels-public.lean') == sha(HERE / (public + '.source.lean'))
source = (HERE / (public + '.source.lean')).read_text()
log = (HERE / (public + '.log')).read_text()
assert len(re.findall(r'^#check @', source, re.M)) == 4
assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == 4
assert len(re.findall(r'^#print axioms ', source, re.M)) == 4
assert not re.search(
    r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|'
    r'uncaught exception|internal exception|maximum recursion depth|maximum number of heartbeats)'
    r'|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|pp\.rawOnError|⋯|…|\.\.\.', log)
reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
assert len(reports) + len(re.findall('does not depend on any axioms', log)) == 4
for report in reports:
    clean = re.sub(r'\.\{[^}]*\}', '', report)
    assert set(re.split(r',\s*', clean.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
for index in range(1, 8):
    meta = json.loads((HERE / f'shared-edit-row-kernels-{index}.json').read_text())
    assert sha(HERE / meta['source']) == meta['sha256']
    assert meta['command'][-1] == str(HERE / meta['source'])
    assert meta['exit_code'] == (0 if index in [5, 7] else 1), index

print(json.dumps({
    'status': 'PASS', 'entries': len(manifest['entries']),
    'constructed_pairs': 4, 'full_proof': True, 'strict_empty': True,
    'source_sha256': sha(HERE / (strict + '.source.lean')),
    'actual_memory_max_high_bytes': 4294967296, 'actual_swap_max_bytes': 0,
}))
