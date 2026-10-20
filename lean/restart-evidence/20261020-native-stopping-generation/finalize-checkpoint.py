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
for name in ['math-review-verification.json',
             'stopping-site-prototype-verification.json', 'prefix-bind-prototype-verification.json',
             'stopping-generation-prototype-verification.json', 'walk-prefix-prototype-verification.json',
             'blocked-fixture-verification.json', 'source-doc-verification.json',
             'next-owner-plan-verification.json']:
    assert read(name)['status'] == 'PASS', name
attempts = []
directories = ['stopping-site-prototype', 'prefix-bind-prototype',
               'stopping-generation-prototype', 'walk-prefix-prototype', 'blocked-fixture']
receipt_paths = list(HERE.glob('*.json'))
receipt_paths += [p for directory in directories for p in (HERE / directory).rglob('*.json')]
for path in sorted(receipt_paths):
    if not re.search(r'(?:-(?:direct|public|canonical|calculation|prefix)-[0-9]+|full-audit-[0-9]+)\.json$', path.name):
        continue
    data = json.loads(path.read_text())
    assert Path(data['command'][0]).name in ['lean', 'lake']
    assert read(str((path.parent / data['limits']).relative_to(HERE))) == {
        'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    assert data['wrapper'][data['wrapper'].index('--mem') + 1] == '4G'
    assert data['wrapper'][data['wrapper'].index('--time') + 1] == '5m'
    attempts.append({'receipt': str(path.relative_to(HERE)), 'exit_code': data['exit_code'],
                     'entered_lean': True, 'reused_from_previous_checkpoint': path.parent.name == 'stopping-site-prototype',
                     'raw_log_bytes': (path.parent / data['log']).stat().st_size})
scope = read('expected-attempt-counts.json')
assert len(attempts) == scope['all_scope_jobs'], (len(attempts), scope)
assert sum(item['exit_code'] != 0 for item in attempts) == scope['all_scope_failures']
assert sum(item['reused_from_previous_checkpoint'] for item in attempts) == 3
write('attempt-accounting.json', {'attempts': attempts, 'wrapper_attempts': len(attempts),
       'entered_lean': len(attempts), 'pre_lean_blocked': 0,
       'elaboration_or_calculation_failures': scope['all_scope_failures'],
       'reused_prior_jobs': 3, 'fresh_jobs': len(attempts) - 3,
       'selected_public_pairs': 4, 'selected_constructed_pairs': 1,
       'review_receipt_copies_do_not_add_jobs': True, 'all_attempts_terminal': True})

prototype_paths = [p for directory in directories[:-1] for p in (HERE / directory).rglob('*') if p.is_file()]
write('prototype-source-manifest.json', {'entries': [entry(p) for p in sorted(prototype_paths)]})
fixture_paths = [p for p in (HERE / 'blocked-fixture').rglob('*') if p.is_file()]
write('blocked-fixture-source-manifest.json', {'entries': [entry(p) for p in sorted(fixture_paths)]})

math_paths = {ROOT / item['path'] for item in read('math-review-source-pins.json')['files']}
math_paths.update(p for directory in ['stopping-prefix-math-review', 'walk-prefix-math-review',
                                    'blocked-fixture-math-review']
                  for p in (HERE / directory).rglob('*') if p.is_file())
math_paths.update(HERE / name for name in ['math-review-source-pins.json', 'math-review-verification.json',
                  'stopping-prefix-math-review-verification.json', 'walk-prefix-math-review-verification.json',
                  'blocked-fixture-math-review-verification.json'])
write('math-source-manifest.json', {'entries': [entry(p) for p in sorted(math_paths)]})

doc_config = read('source-doc-source-pins.json')
doc_paths = {ROOT / item['path'] for item in doc_config['files']}
doc_paths.update(HERE / item['path'] for item in doc_config['artifacts'])
doc_paths.update(HERE / name for name in ['source-doc-ranges.json', 'source-doc-source-pins.json',
    'source-doc-verify.py', 'source-doc-review.md', 'source-doc-verification.json'])
write('source-doc-manifest.json', {'entries': [entry(p) for p in sorted(doc_paths)]})

names = ['root-run-check.py', 'root-capped-worker.py', 'root-review.md', 'root-peaks.txt',
         'verify-probes.py', 'proof-commit.txt', 'public-heads.json', 'new-modules.json',
         'frozen-modules.json', 'expected-counts.json', 'expected-attempt-counts.json', 'selected-audit.json',
         'selected-strict.json', 'selected-canonical.json', 'selected-canonical-warnings.json',
         'selected-constructed-strict.json', 'selected-groups.json', 'selection-status.json',
         'next-compiled-owner-handoff.md', 'previous-checkpoint-board-read.json',
         'previous-publication.json', 'previous-closure.json', 'previous-closure-limits.json',
         'previous-closure-peaks.txt']
root_paths = {ROOT / 'lean/MicroCFTA' / (name + '.lean') for name in read('new-modules.json')}
root_paths.update(HERE / name for name in names)
root_paths.update(p for p in HERE.iterdir() if p.is_file() and
                  p.name.startswith(('stopping-site-official-', 'prefix-bind-official-',
                                     'stopping-generation-official-', 'walk-prefix-official-',
                                     'foundations-official-', 'full-audit-')))
write('root-source-manifest.json', {'entries': [entry(p) for p in sorted(root_paths)]})
future_paths = [p for p in (HERE / 'next-owner-plan').rglob('*') if p.is_file()]
future_paths.extend(HERE / name for name in ['next-owner-plan-verification.json', 'next-owner-unbound-request-review.md'])
write('next-source-manifest.json', {'entries': [entry(p) for p in sorted(future_paths)]})
write('component-manifests.json', ['root-source-manifest.json', 'prototype-source-manifest.json',
                                  'blocked-fixture-source-manifest.json', 'math-source-manifest.json',
                                  'source-doc-manifest.json', 'next-source-manifest.json'])
env = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}
for script, output in [('verify-checkpoint.py', 'checkpoint-validation.json'),
                       ('verify-preservation.py', 'preservation-final.json')]:
    data = subprocess.check_output([sys.executable, str(HERE / script)], cwd=ROOT, env=env)
    assert json.loads(data)['status'] == 'PASS'
    (HERE / output).write_bytes(data)
print(json.dumps({'checkpoint': read('checkpoint-validation.json'),
                  'preservation': {k: v for k, v in read('preservation-final.json').items()
                                   if k != 'frozen_manifests'},
                  'actual_lean_jobs': len(attempts), 'failures': scope['all_scope_failures']}, indent=2))
