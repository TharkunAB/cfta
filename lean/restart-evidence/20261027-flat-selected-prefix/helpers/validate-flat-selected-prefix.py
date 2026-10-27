from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-selected-prefix-20261027')


def digest(data):
    return hashlib.sha256(data).hexdigest()


modules = json.loads((area / 'modules.json').read_text())
checks = json.loads((area / 'strict-checks.json').read_text())
assert set(checks) == set(modules + ['Audit'])
records = []
for module, check in checks.items():
    folder = area / check
    report = json.loads((folder / 'report.json').read_text())
    data = (root / 'lean/MicroCFTA' / (module + '.lean')).read_bytes()
    assert data == (folder / 'MicroCFTA' / (module + '.lean')).read_bytes()
    assert digest(data) == report['source_sha256']
    raw = (folder / 'raw.log').read_bytes()
    assert digest(raw) == report['sha256'] and len(raw) == report['bytes']
    assert report['exit_code'] == 0
    assert report['cgroup_limits'] == {'memory.max': '4294967296',
        'memory.high': '4294967296', 'memory.swap.max': '0'}
    if module != 'Audit':
        assert not raw
        assert not re.search(rb'\b(sorry|admit|axiom|native_decide)\b', data)
        assert b'maxHeartbeats' not in data
    records.append({'module': module, 'check': check, 'bytes': len(data), 'sha256': digest(data)})

base = (area / 'published-base.txt').read_text().strip()
changed = subprocess.check_output(['git', 'diff', '--name-only', '-z', base], cwd=root).split(b'\0')
changed = [item.decode() for item in changed if item]
assert all(not item.endswith(('.hs', '.cabal')) for item in changed), changed
allowed_sources = {'lean/MicroCFTA/' + module + '.lean' for module in modules + ['Audit']}
assert all(not item.startswith('lean/MicroCFTA/') or item in allowed_sources for item in changed), changed
old_audit = (area / 'prior-audit.lean').read_bytes()
new_audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert new_audit == b''.join(('import MicroCFTA.' + module + '\n').encode() for module in modules) + old_audit
for module, expected in [
    ('SourceCurrentColdFiniteWarmCalls', 'e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'),
    ('SourcePruningEnumerationCapturedRendering', '18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386')]:
    path = 'lean/MicroCFTA/' + module + '.lean'
    data = (root / path).read_bytes()
    assert digest(data) == expected
    assert data == subprocess.check_output(['git', 'show', base + ':' + path], cwd=root)

for module in modules + ['Audit', 'SourceCurrentColdFiniteWarmCalls', 'SourcePruningEnumerationCapturedRendering']:
    relative = Path('lean/MicroCFTA') / (module + '.lean')
    target = area / 'installed-sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((root / relative).read_bytes())

report = {'status': 'pass', 'strict_checks': records, 'unchanged_global_theorems': 2,
    'no_haskell_changes': True, 'audit_only_adds_imports': True}
(area / 'source-validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': 'pass', 'strict_checks': len(checks)}))
