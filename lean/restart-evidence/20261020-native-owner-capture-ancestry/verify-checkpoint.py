import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


checks = runpy.run_path(str(HERE / 'verify-probes.py'))
assert read('selection-status.json')['finalized']
expected = read('expected-counts.json')
groups = read('selected-groups.json')
assert len({group['name'] for group in groups}) == len(groups)
counts = {kind: sum(group['pairs'] for group in groups if group['kind'] == kind)
          for kind in ['new-public', 'constructed', 'private-claim']}
assert counts == expected['pairs']
for group in groups:
    checks['check_group'](group)
modules = read('frozen-modules.json')
assert len(modules) == expected['modules']
assert list(modules) == read('new-modules.json')
assert set(read('selected-strict.json')) == set(modules)
assert set(read('selected-canonical.json')) == set(modules)
proof = (HERE / 'proof-commit.txt').read_text().strip()
subprocess.run(['git', 'merge-base', '--is-ancestor', proof, 'HEAD'], cwd=ROOT, check=True)
heads = []
for module, digest in modules.items():
    path = ROOT / 'lean/MicroCFTA' / (module + '.lean')
    assert sha(path) == digest
    committed = subprocess.check_output(['git', 'show', proof + ':' + str(path.relative_to(ROOT))], cwd=ROOT)
    assert hashlib.sha256(committed).hexdigest() == digest
    names = re.findall(r'^(?:theorem|def|structure|inductive) (\u00ab[^\u00bb]+\u00bb|[A-Za-z0-9_.]+)', path.read_text(), re.M)
    heads.extend('MicroCFTA.' + module + '.' + name.strip('\u00ab\u00bb') for name in names)
checked = []
for group in groups:
    if group['kind'] == 'new-public':
        meta = read(group['name'] + '.json')
        base = (HERE / (group['name'] + '.json')).parent
        checked.extend(re.findall(r'^#check @([^\s]+)', (base / meta['source']).read_text(), re.M))
assert heads == read('public-heads.json')
assert len(heads) == len(checked) == counts['new-public'] and set(heads) == set(checked)
for module, stem in read('selected-strict.json').items():
    meta = read(stem + '.json')
    assert meta['exit_code'] == 0 and not (HERE / meta['log']).read_bytes()
    assert sha(HERE / meta['source']) == modules[module]
    checks['check_limits'](stem)
for stem, source in read('selected-constructed-strict.json').items():
    meta = read(stem + '.json')
    assert meta['exit_code'] == 0 and not (HERE / meta['log']).read_bytes()
    assert sha(HERE / meta['source']) == sha(HERE / source) == meta['sha256']
    checks['check_limits'](stem)
assert len(read('selected-constructed-strict.json')) == expected['constructed_strict']
old_log = (ROOT / 'lean/restart-evidence/20261019-head-issued-paths/full-audit-1.log').read_text()
old_warnings = re.findall(r'^warning:.*$', old_log, re.M)
assert len(old_warnings) == 1
for module, stem in read('selected-canonical.json').items():
    meta = read(stem + '.json')
    log = (HERE / meta['log']).read_text()
    assert meta['exit_code'] == 0 and 'Build completed successfully' in log
    assert re.findall(r'^warning:.*$', log, re.M) == read('selected-canonical-warnings.json')[module]
    assert read('selected-canonical-warnings.json')[module] in [[], old_warnings]
    checks['check_limits'](stem)
audit = read('selected-audit.json')
meta = read(audit['name'] + '.json')
log = (HERE / meta['log']).read_text()
assert meta['exit_code'] == 0
assert f"Build completed successfully ({audit['jobs']} jobs)." in log
assert f"Checked axiom dependencies of {audit['dependency_checks']} MicroCFTA theorems." in log
assert re.findall(r'^warning:.*$', log, re.M) == old_warnings
assert audit['jobs'] == expected['audit_jobs'] and audit['dependency_checks'] == expected['audit_dependency_checks']
checks['check_limits'](audit['name'])
environment = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}
for item in read('component-verifiers.json'):
    result = json.loads(subprocess.check_output([sys.executable, str(HERE / item['path']), *item['arguments']],
                                               cwd='/', env=environment))
    assert result['status'] == 'PASS', item['path']
for entry in read('capture-consistency-audit/source-audit-pins.json')['files']:
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
unique = {}
diagnostics = read('non-json-evidence.json')
observed_diagnostics = set()
for path in HERE.rglob('*.json'):
    try:
        data = json.loads(path.read_text())
    except ValueError:
        name = str(path.relative_to(HERE))
        assert name in diagnostics and sha(path) == diagnostics[name], name
        observed_diagnostics.add(name)
        continue
    if (isinstance(data, dict) and isinstance(data.get('command'), list)
            and isinstance(data.get('exit_code'), int) and 'wrapper' in data
            and Path(data['command'][0]).name in ['lean', 'lake']):
        unique.setdefault(json.dumps(data, sort_keys=True), []).append(str(path.relative_to(HERE)))
accounting = read('attempt-accounting.json')
assert observed_diagnostics == set(diagnostics)
assert len(unique) == accounting['capped_commands']
assert sum(json.loads(key)['exit_code'] != 0 for key in unique) == accounting['failed_commands']
for key, paths in unique.items():
    data = json.loads(key)
    for name in paths:
        base = (HERE / name).parent
        assert (base / data['log']).exists()
        assert read(str((base / data['limits']).relative_to(HERE))) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        if 'source' in data:
            assert sha(base / data['source']) == data['sha256']
print(json.dumps({'status': 'PASS', 'proof_commit': proof, 'modules': len(modules),
                  'public_pairs': counts['new-public'], 'constructed_pairs': counts['constructed'],
                  'capped_commands': len(unique), 'failed_commands': accounting['failed_commands'],
                  'audit_jobs': audit['jobs'], 'audit_dependency_checks': audit['dependency_checks']}, indent=2))
