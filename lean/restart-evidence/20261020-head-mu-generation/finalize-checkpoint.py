import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')


def entry(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(ROOT)), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


assert read('selection-status.json')['finalized']
for name in ['math-review-verification.json', 'prototype-verification.json',
             'fixture-verification.json', 'source-doc-verification.json',
             'stopping-interface-verification.json']:
    assert read(name)['status'] == 'PASS', name
attempts = []
for path in sorted(HERE.rglob('*.json')):
    if not re.search(r'(?:-(?:direct|public|canonical)-[0-9]+|full-audit-[0-9]+)\.json$', path.name):
        continue
    data = json.loads(path.read_text())
    assert Path(data['command'][0]).name in ['lean', 'lake']
    assert read(str((path.parent / data['limits']).relative_to(HERE))) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    assert data['wrapper'][data['wrapper'].index('--mem') + 1] == '4G'
    assert data['wrapper'][data['wrapper'].index('--time') + 1] == '5m'
    attempts.append({'receipt': str(path.relative_to(HERE)), 'exit_code': data['exit_code'],
                     'entered_lean': True,
                     'raw_log_bytes': (path.parent / data['log']).stat().st_size})
assert len(attempts) == 9, len(attempts)
assert sum(item['exit_code'] != 0 for item in attempts) == 1
write('attempt-accounting.json', {'attempts': attempts, 'wrapper_attempts': 9,
       'entered_lean': 9, 'pre_lean_blocked': 0, 'elaboration_failures': 1,
       'selected_public_pairs': 1, 'selected_constructed_pairs': 1,
       'proof_pair_count_excludes_reviews_and_reused_prototypes': True,
       'all_attempts_terminal': True})

for label, original_name, prefix in [
    ('prototype', '/tmp/mcfta-head-mu-generation', 'prototype'),
    ('fixture', '/tmp/mcfta-head-mu-generation-fixture', '')]:
    paths = []
    original = Path(original_name)
    for path in original.rglob('*'):
        if path.is_file():
            copied = HERE / prefix / path.relative_to(original)
            assert copied.read_bytes() == path.read_bytes(), copied
            paths.append(copied)
    write(label + '-source-manifest.json', {'entries': [entry(p) for p in sorted(paths)]})

math_paths = {ROOT / item['path'] for item in read('math-review-source-pins.json')['files']}
stopping = read('mcfta-stopping-build-rooted-writers-interface-review-source-pins.json')
math_paths.update(ROOT / item['path'] for item in stopping['files'])
math_paths.update(p for p in HERE.iterdir() if p.is_file() and
                  p.name.startswith(('mcfta-', 'math-review-', 'stopping-interface-')))
write('math-source-manifest.json', {'entries': [entry(p) for p in sorted(math_paths)]})

doc_config = read('source-doc-source-pins.json')
doc_paths = {ROOT / item['path'] for item in doc_config['files']}
doc_paths.update(HERE / item['path'] for item in doc_config['artifacts'])
doc_paths.update(HERE / name for name in ['source-doc-ranges.json', 'source-doc-source-pins.json',
    'source-doc-verify.py', 'source-doc-review.md', 'source-doc-verification.json'])
write('source-doc-manifest.json', {'entries': [entry(p) for p in sorted(doc_paths)]})

names = ['root-run-check.py', 'root-capped-worker.py', 'root-review.md', 'root-peaks.txt',
         'verify-probes.py', 'proof-commit.txt', 'public-heads.json', 'new-modules.json',
         'frozen-modules.json', 'expected-counts.json', 'selected-audit.json',
         'selected-strict.json', 'selected-canonical.json', 'selected-canonical-warnings.json',
         'selected-constructed-strict.json', 'selected-groups.json', 'selection-status.json',
         'next-native-generation-handoff.md', 'next-source-leaf-general-composition-review.md',
         'previous-checkpoint-board-read.json', 'previous-publication.json',
         'previous-closure.json', 'previous-closure-limits.json', 'previous-closure-peaks.txt']
root_paths = {ROOT / 'lean/MicroCFTA' / (name + '.lean') for name in read('new-modules.json')}
root_paths.update(HERE / name for name in names)
root_paths.update(p for p in HERE.iterdir() if p.is_file() and
                  p.name.startswith(('head-official-', 'full-audit-')))
write('root-source-manifest.json', {'entries': [entry(p) for p in sorted(root_paths)]})
write('component-manifests.json', ['root-source-manifest.json', 'prototype-source-manifest.json',
                                  'fixture-source-manifest.json', 'math-source-manifest.json',
                                  'source-doc-manifest.json'])
env = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}
for script, output in [('verify-checkpoint.py', 'checkpoint-validation.json'),
                       ('verify-preservation.py', 'preservation-final.json')]:
    data = subprocess.check_output([sys.executable, str(HERE / script)], cwd=ROOT, env=env)
    assert json.loads(data)['status'] == 'PASS'
    (HERE / output).write_bytes(data)
print(json.dumps({'checkpoint': read('checkpoint-validation.json'),
                  'preservation': {k: v for k, v in read('preservation-final.json').items()
                                   if k != 'frozen_manifests'},
                  'actual_lean_jobs': 9, 'elaboration_failures': 1}, indent=2))
