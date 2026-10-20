import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-indexed-first-ordinary-cut'


def read(name):
    return json.loads((HERE / name).read_text())


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


def entry(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(ROOT)), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


assert read('selection-status.json')['finalized']
for name in ['math-review-verification.json', 'source-doc-verification.json',
             'fixture-verification.json', 'cut-prototype-verification.json',
             'source-cases-prototype-verification.json']:
    assert read(name)['status'] == 'PASS', name
attempts = []
for path in sorted(HERE.rglob('*.json')):
    if not re.search(r'(?:-(?:direct|public|canonical)-[0-9]+|full-audit-[0-9]+)\.json$', path.name):
        continue
    data = json.loads(path.read_text())
    assert Path(data['command'][0]).name in ['lean', 'lake']
    log = path.parent / data['log']
    limit_path = path.parent / data['limits']
    blocked = path.relative_to(HERE).as_posix() == 'cut-prototype/cut-direct-1.json'
    if blocked:
        assert data['exit_code'] != 0 and not limit_path.exists()
        assert log.read_text() == 'Failed to connect to bus: Operation not permitted\n'
    else:
        assert json.loads(limit_path.read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    attempts.append({'receipt': str(path.relative_to(HERE)), 'exit_code': data['exit_code'],
                     'entered_lean': not blocked, 'raw_log_bytes': log.stat().st_size})
assert len(attempts) == 17, len(attempts)
assert sum(item['entered_lean'] for item in attempts) == 16
assert sum(item['entered_lean'] and item['exit_code'] != 0 for item in attempts) == 3
write('attempt-accounting.json', {
    'attempts': attempts, 'wrapper_attempts': len(attempts), 'entered_lean': 16,
    'pre_lean_blocked': 1, 'elaboration_failures': 3,
    'selected_public_pairs': 4, 'selected_constructed_pairs': 1,
    'proof_pair_count_excludes_reviews_and_reused_prototypes': True,
    'all_attempts_terminal': True})

prototype_paths = []
for dirname, original in [('cut-prototype', '/tmp/mcfta-indexed-first-ordinary-cut'),
                          ('source-cases-prototype', '/tmp/mcfta-indexed-leaf-source-rows')]:
    for path in Path(original).rglob('*'):
        if path.is_file():
            copied = HERE / dirname / path.relative_to(original)
            assert copied.read_bytes() == path.read_bytes(), copied
            prototype_paths.append(copied)
write('prototype-source-manifest.json', {'entries': [entry(p) for p in sorted(prototype_paths)]})

fixture_paths = []
original = Path('/tmp/mcfta-indexed-first-ordinary-cut-fixture')
for path in original.rglob('*'):
    if path.is_file():
        copied = HERE / path.relative_to(original)
        assert copied.read_bytes() == path.read_bytes()
        fixture_paths.append(copied)
write('fixture-source-manifest.json', {'entries': [entry(p) for p in sorted(fixture_paths)]})

math_paths = {ROOT / item['path'] for item in read('math-review-source-pins.json')['files']}
math_paths.update(p for p in HERE.iterdir() if p.is_file() and
                  (p.name.startswith('mcfta-') or p.name.startswith('math-review-')))
write('math-source-manifest.json', {'entries': [entry(p) for p in sorted(math_paths)]})

doc_config = read('source-doc-source-pins.json')
doc_paths = {ROOT / item['path'] for item in doc_config['files']}
doc_paths.update(HERE / item['path'] for item in doc_config['artifacts'])
doc_paths.update(HERE / n for n in ['source-doc-ranges.json', 'source-doc-source-pins.json',
                                  'source-doc-verify.py', 'source-doc-review.md',
                                  'source-doc-verification.json'])
write('source-doc-manifest.json', {'entries': [entry(p) for p in sorted(doc_paths)]})

names = ['root-run-check.py', 'root-capped-worker.py', 'root-review.md', 'root-peaks.txt',
         'root-final-peaks.txt', 'verify-probes.py', 'proof-commit.txt', 'public-heads.json',
         'new-modules.json', 'frozen-modules.json', 'expected-counts.json', 'selected-audit.json',
         'selected-strict.json', 'selected-canonical.json', 'selected-canonical-warnings.json',
         'selected-constructed-strict.json', 'selected-groups.json', 'selection-status.json',
         'next-binding-ancestry-handoff.md', 'next-source-leaf-general-composition-review.md',
         'previous-checkpoint-board-read.json', 'previous-publication.json', 'previous-closure.json',
         'previous-closure-limits.json', 'previous-closure-peaks.txt']
root_paths = {ROOT / 'lean/MicroCFTA' / (m + '.lean') for m in read('new-modules.json')}
root_paths.update(HERE / name for name in names)
root_paths.update(p for p in HERE.iterdir() if p.is_file() and p.name.startswith(
    ('cut-official-', 'source-cases-official-', 'full-audit-')))
write('root-source-manifest.json', {'entries': [entry(p) for p in sorted(root_paths)]})
write('component-manifests.json', ['root-source-manifest.json', 'prototype-source-manifest.json',
                                   'fixture-source-manifest.json', 'math-source-manifest.json',
                                   'source-doc-manifest.json'])
env = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}
for script, out in [('verify-checkpoint.py', 'checkpoint-validation.json'),
                    ('verify-preservation.py', 'preservation-final.json')]:
    data = subprocess.check_output([sys.executable, str(HERE / script)], cwd=ROOT, env=env)
    assert json.loads(data)['status'] == 'PASS'
    (HERE / out).write_bytes(data)
print(json.dumps({'checkpoint': read('checkpoint-validation.json'),
                  'preservation': {k: v for k, v in read('preservation-final.json').items()
                                   if k != 'frozen_manifests'},
                  'wrapper_attempts': 17, 'actual_lean_jobs': 16,
                  'pre_lean_bus_denials': 1, 'elaboration_failures': 3}, indent=2))
