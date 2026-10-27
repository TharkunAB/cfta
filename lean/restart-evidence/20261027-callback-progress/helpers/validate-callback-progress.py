from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-callback-progress-20261027')


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
        code = re.sub(rb'/-.*?-/', b'', data, flags=re.S)
        code = re.sub(rb'--[^\n]*', b'', code)
        # Admit is also an existing worklist constructor. This pattern is a case, not a tactic.
        code = re.sub(rb'(?m)^([ \t]*\|[ \t]*)@admit(?=[ \t])', rb'\1@worklistConstructor', code)
        assert not re.search(rb'\b(sorry|admit|axiom|native_decide)\b', code)
        assert b'maxHeartbeats' not in data
    records.append({'module': module, 'check': check, 'bytes': len(data), 'sha256': digest(data)})

base = (area / 'published-base.txt').read_text().strip()
changed = subprocess.check_output(['git', 'diff', '--name-only', '-z', base], cwd=root).split(b'\0')
changed = [item.decode() for item in changed if item]
assert all(not item.endswith(('.hs', '.cabal')) for item in changed), changed
allowed_sources = {'lean/MicroCFTA/' + module + '.lean' for module in modules + ['Audit']}
assert all(not item.startswith('lean/MicroCFTA/') or item in allowed_sources for item in changed), changed
old_audit = (area / 'prior-sources/Audit.lean').read_bytes()
assert old_audit == subprocess.check_output(['git', 'show', base + ':lean/MicroCFTA/Audit.lean'], cwd=root)
new_audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
repair = json.loads((area / 'audit-import-insertion.json').read_text())
offset = repair['insertion_offset']
extra = b''.join(('import MicroCFTA.' + module + '\n').encode() for module in modules)
assert new_audit == old_audit[:offset] + extra + old_audit[offset:]
prior_sources = json.loads((area / 'prior-strong-sources.json').read_text())
for record in prior_sources:
    data = (root / record['path']).read_bytes()
    assert len(data) == record['bytes'] and digest(data) == record['sha256']
    assert data == subprocess.check_output(['git', 'show', base + ':' + record['path']], cwd=root)

for module in modules + ['Audit'] + [record['module'] for record in prior_sources]:
    relative = Path('lean/MicroCFTA') / (module + '.lean')
    target = area / 'installed-sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((root / relative).read_bytes())

report = {'status': 'pass', 'strict_checks': records, 'unchanged_prior_theorems': len(json.loads((area / 'prior-public-declarations.json').read_text())),
    'no_haskell_source_changes': True, 'audit_only_adds_imports': True}
(area / 'source-validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': 'pass', 'strict_checks': len(checks)}))
