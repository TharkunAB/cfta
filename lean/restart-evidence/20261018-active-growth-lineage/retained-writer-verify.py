#!/usr/bin/env python3
import gzip
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    result = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(1048576), b''):
            result.update(block)
    return result.hexdigest()


def probe(stem, count):
    source = (HERE / (stem + '.source.lean')).read_text()
    log = (HERE / (stem + '.log')).read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true',
                   'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
                   'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in source, (stem, option)
    assert len(re.findall(r'^#check @', source, re.M)) == count, stem
    assert len(re.findall(r'^#print (?!axioms )', source, re.M)) == count, stem
    assert len(re.findall(r'^#print axioms ', source, re.M)) == count, stem
    assert not re.search(r'(?i:failed to pretty print|pretty.?print[^\n]*(?:error|fail|exception)|uncaught exception|internal exception|maximum recursion depth|maximum number of heartbeats)|sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|pp\.rawOnError|⋯|…|\.\.\.', log), stem
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(axioms) + len(re.findall('does not depend on any axioms', log)) == count, stem
    for used in axioms:
        used = re.sub(r'\.\{[^}]*\}', '', used)
        assert set(re.split(r',\s*', used.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, used


manifest = json.loads((HERE / 'retained-writer-manifest.json').read_text())
for entry in manifest['entries']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
production = manifest['productions'][0]
assert sha(ROOT / production['path']) == production['sha256']
assert sha(HERE / production['strict_snapshot']) == production['sha256']
for stem in manifest['selected_runs']:
    meta = json.loads((HERE / (stem + '.json')).read_text())
    assert meta['exit_code'] == 0, stem
    assert json.loads((HERE / meta['limits']).read_text()) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}, stem
    if 'source' in meta:
        source = HERE / meta['source']
        assert sha(source) == meta['sha256'], stem
        assert meta['command'] == [
            '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
            '-Dlinter.all=true', str(source)], stem
for stem in ['retained-writer-direct-5', 'retained-writer-kernels-3']:
    assert (HERE / (stem + '.log')).stat().st_size == 0, stem
canonical = (HERE / 'retained-writer-canonical-2.log').read_text()
assert 'Build completed successfully (630 jobs).' in canonical
assert not re.search(r'\b(?:warning|error):', canonical)
probe('retained-writer-public-2', 7)
probe('retained-writer-kernels-public-1', 2)
for live, snapshot in [
    ('retained-writer-public.lean', 'retained-writer-public-2.source.lean'),
    ('retained-writer-kernels.lean', 'retained-writer-kernels-3.source.lean'),
    ('retained-writer-kernels-public.lean', 'retained-writer-kernels-public-1.source.lean')]:
    assert sha(HERE / live) == sha(HERE / snapshot)

archives = json.loads((HERE / 'raw-log-archives.json').read_text())
archived = {entry['original_log']: entry for entry in archives}
for entry in archives:
    compressed = HERE / entry['archive']
    assert sha(compressed) == entry['archive_sha256']
    assert compressed.stat().st_size == entry['archive_bytes']
    digest = hashlib.sha256()
    size = 0
    with gzip.open(compressed, 'rb') as source:
        for block in iter(lambda: source.read(1048576), b''):
            digest.update(block)
            size += len(block)
    assert digest.hexdigest() == entry['original_sha256']
    assert size == entry['original_bytes']
    assert sha(HERE / entry['failed_run_metadata']) == entry['failed_run_metadata_sha256']
for path in HERE.glob('retained-writer-*.json'):
    if path.name.endswith('.limits.json') or path.name == 'retained-writer-manifest.json':
        continue
    meta = json.loads(path.read_text())
    if 'command' in meta and 'source' in meta:
        assert sha(HERE / meta['source']) == meta['sha256'], path.name
        assert (HERE / meta['log']).exists() or meta['log'] in archived, path.name
assert (HERE / 'retained-writer-direct-4.log').stat().st_size == 369
assert 'This simp argument is unused' in (HERE / 'retained-writer-direct-4.log').read_text()
assert json.loads((HERE / 'retained-writer-kernels-1.json').read_text())['exit_code'] == 1
assert json.loads((HERE / 'retained-writer-kernels-2.json').read_text())['exit_code'] == 1
print(json.dumps(dict(status='PASS', entries=len(manifest['entries']), public_pairs=7,
                      constructed_pairs=2, full_proof=True, strict_empty=True,
                      production_sha256=production['sha256'], archived_failed_logs=len(archives),
                      memory_max_high_bytes=4294967296, swap_max_bytes=0)))
