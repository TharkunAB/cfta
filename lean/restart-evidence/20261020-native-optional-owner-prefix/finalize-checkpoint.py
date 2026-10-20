import hashlib
import json
import os
from pathlib import Path
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
assert read('attempt-accounting.json')['capped_commands'] == 62
assert read('attempt-accounting.json')['failed_commands'] == 17

prototypes = ['optional-prefix-prototype', 'query-prefix-prototype',
              'mu-prefix-prototype', 'walk-prefix-prototype',
              'edge-prefix-prototype', 'compiler-prefix-prototype',
              'key-exclusion-snippet']
reviews = ['architecture-review', 'query-math-review', 'owner-mu-math-review',
           'compiler-edge-math-review', 'owner-final-math-review',
           'owner-draft-math-review', 'compiled-fixture-math-review']
verifiers = {
    'optional-prefix-prototype': 'optional-prefix-verify.py',
    'query-prefix-prototype': 'query-prefix-verify.py',
    'mu-prefix-prototype': 'mu-prefix-verify.py',
    'walk-prefix-prototype': 'walk-optional-verify.py',
    'edge-prefix-prototype': 'edge-prefix-verify.py',
    'compiler-prefix-prototype': 'compiler-prefix-verify.py',
    'key-exclusion-snippet': 'owner-key-verify.py',
    'compiled-owner-fixture': 'owner-kernels-verify.py',
    'architecture-review': 'verify.py',
    'query-math-review': 'verify.py',
    'owner-mu-math-review': 'verify.py',
    'compiler-edge-math-review': 'math-review-verify.py',
    'owner-final-math-review': 'math-review-verify.py',
    'compiled-fixture-math-review': 'math-review-verify.py',
    'source-doc-warning-amendment': 'amendment-verify.py',
}
environment = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}
for directory, script in verifiers.items():
    result = subprocess.check_output([sys.executable, str(HERE / directory / script)],
                                     cwd=ROOT, env=environment)
    assert json.loads(result)['status'] == 'PASS', directory
    write(directory + '-verification.json', json.loads(result))
assert read('source-doc-verification.json')['status'] == 'PASS'
for arguments, retained in [([], 'source-doc-verification.json'),
                             (['--live'], 'source-doc-live-verification.json')]:
    result = subprocess.check_output([sys.executable, str(HERE / 'source-doc-verify.py'),
                                      '--root', str(ROOT), *arguments], cwd=ROOT, env=environment)
    assert json.loads(result) == read(retained)


def directory_files(names):
    return {path for name in names for path in (HERE / name).rglob('*') if path.is_file()}


prototype_paths = directory_files(prototypes)
write('prototype-source-manifest.json', {'entries': [entry(p) for p in sorted(prototype_paths)]})
fixture_paths = directory_files(['compiled-owner-fixture'])
write('fixture-source-manifest.json', {'entries': [entry(p) for p in sorted(fixture_paths)]})

math_paths = directory_files(reviews)
math_paths.update(HERE / (name + '-verification.json') for name in reviews
                  if (HERE / (name + '-verification.json')).exists())
math_paths.update(ROOT / record['path'] for record in read('math-review-source-pins.json')['files'])
math_paths.add(HERE / 'math-review-source-pins.json')
write('math-source-manifest.json', {'entries': [entry(p) for p in sorted(math_paths)]})

configuration = read('source-doc-source-pins.json')
doc_paths = {ROOT / item['path'] for item in configuration['files']}
doc_paths.update(HERE / item['path'] for item in configuration['artifacts'])
doc_paths.update(p for p in HERE.iterdir() if p.is_file() and p.name.startswith('source-doc-')
                 and p.name != 'source-doc-manifest.json')
doc_paths.update(directory_files(['source-doc-warning-amendment']))
write('source-doc-manifest.json', {'entries': [entry(p) for p in sorted(doc_paths)]})

excluded = {'SHA256SUMS', 'root-scope-manifest.json', 'checkpoint-validation.json',
            'preservation-final.json', 'whitespace-policy.json', 'component-manifests.json',
            'root-source-manifest.json', 'prototype-source-manifest.json',
            'fixture-source-manifest.json', 'math-source-manifest.json',
            'source-doc-manifest.json'}
root_paths = {ROOT / 'lean/MicroCFTA' / (name + '.lean') for name in read('new-modules.json')}
root_paths.update(p for p in HERE.iterdir() if p.is_file() and p.name not in excluded
                  and not p.name.startswith('source-doc-'))
write('root-source-manifest.json', {'entries': [entry(p) for p in sorted(root_paths)]})
write('component-manifests.json', ['root-source-manifest.json', 'prototype-source-manifest.json',
                                 'fixture-source-manifest.json', 'math-source-manifest.json',
                                 'source-doc-manifest.json'])

for script, output in [('verify-checkpoint.py', 'checkpoint-validation.json'),
                       ('verify-preservation.py', 'preservation-final.json')]:
    data = subprocess.check_output([sys.executable, str(HERE / script)], cwd=ROOT, env=environment)
    assert json.loads(data)['status'] == 'PASS'
    (HERE / output).write_bytes(data)
print(json.dumps({'status': 'PASS', 'proof_commit': (HERE / 'proof-commit.txt').read_text().strip(),
                  'public_pairs': 12, 'constructed_pairs': 1, 'capped_commands': 62,
                  'failed_commands': 17, 'modules': 9, 'audit_jobs': 3504,
                  'audit_dependency_checks': 74153}))
