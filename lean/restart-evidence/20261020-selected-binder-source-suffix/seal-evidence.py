import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-selected-binder-source-suffix'


def entry(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(ROOT)),
            'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


assert json.loads((HERE / 'checkpoint-validation.json').read_text())['status'] == 'PASS'
assert not list(HERE.rglob('*.pyc'))
assert 'still under validation' not in (HERE / 'README.md').read_text()
assert 'Final fixture selection, review pins and checkpoint closure are pending.' not in (HERE / 'README.md').read_text()
assert subprocess.run(['git', 'diff', '--check'], cwd=ROOT, capture_output=True).returncode == 0
exceptions = []
for path in sorted(HERE.rglob('*')):
    if not path.is_file():
        continue
    check = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(path)],
                           cwd=ROOT, capture_output=True, text=True)
    assert not check.stderr, (path, check.stderr)
    if not check.stdout:
        continue
    lines = check.stdout.splitlines()
    issues = sorted({line.split(': ', 1)[1] for line in lines if ': ' in line and
                     ('trailing whitespace' in line or 'blank line at EOF' in line or 'space before tab' in line)})
    assert issues, (path, check.stdout)
    exceptions.append({'path': str(path.relative_to(ROOT)), 'issues': issues,
                       'policy': 'Preserve exact immutable attempt, printer, log or copied status bytes.'})
write('whitespace-policy.json', {
    'production_and_current_document_diff_check': 'git diff --check passed',
    'immutable_evidence_exceptions': exceptions,
    'all_exception_files_under_current_evidence_directory': True})

docs = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
        'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
        'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md',
        'lean/notes-current-selected-binder-source-suffix.md', 'lean/MicroCFTA/Audit.lean']
modules = json.loads((HERE / 'frozen-modules.json').read_text())
paths = [ROOT / name for name in docs]
paths += [ROOT / 'lean/MicroCFTA' / (name + '.lean') for name in modules]
names = ['verify-checkpoint.py', 'verify-preservation.py', 'verify-closure.py',
         'verify-probes.py', 'checkpoint-validation.json', 'preservation-final.json',
         'proof-commit.txt', 'selected-audit.json', 'selected-groups.json',
         'selected-strict.json', 'selected-canonical.json', 'selected-canonical-warnings.json',
         'selected-constructed-strict.json', 'new-modules.json', 'frozen-modules.json',
         'expected-counts.json', 'component-manifests.json', 'public-heads.json',
         'selection-status.json', 'README.md', 'next-binding-ancestry-handoff.md',
         'current-status-block.md', 'attempt-accounting.json', 'upstream-refresh.json',
         'findings-update.md', 'root-review.md', 'root-final-peaks.txt',
         'source-doc-ranges.json', 'whitespace-policy.json']
names += json.loads((HERE / 'component-manifests.json').read_text())
names += ['mcfta-native-capture-original-root-gap-review.md',
          'mcfta-native-capture-original-root-gap-review-source-pins.json',
          'native-generation-gap-verification.json']
paths += [HERE / name for name in names]
write('root-scope-manifest.json', {'entries': [entry(path) for path in paths]})
files = [p for p in sorted(HERE.rglob('*')) if p.is_file() and p.name != 'SHA256SUMS']
(HERE / 'SHA256SUMS').write_text(''.join(
    hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + str(p.relative_to(ROOT)) + '\n' for p in files))
print(json.dumps({'scope_pins': len(paths), 'evidence_checksums': len(files),
                  'immutable_whitespace_exceptions': len(exceptions)}, indent=2))
