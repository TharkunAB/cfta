from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-pruning-callback-20261027')

def digest(data):
    return hashlib.sha256(data).hexdigest()

records = []
for pins in sorted(area.glob('*/source-pins.json')):
    def visit(value):
        if isinstance(value, list):
            for item in value:
                visit(item)
        elif isinstance(value, dict):
            snapshot = value.get('snapshot', value.get('copy_path'))
            original = value.get('source', value.get('source_path'))
            if snapshot and original and 'sha256' in value:
                copied = Path(snapshot)
                if not copied.is_absolute():
                    copied = pins.parent / copied
                data = copied.read_bytes()
                assert digest(data) == value['sha256'], copied
                assert len(data) == value['bytes'], copied
                source = Path(original)
                if not source.is_absolute():
                    source = root / source
                live = source.read_bytes()
                first = value.get('first_line', value.get('first'))
                last = value.get('last_line', value.get('last'))
                if first is not None:
                    live = b''.join(live.splitlines(keepends=True)[first-1:last])
                assert live == data, (source, copied)
                records.append({'pins': str(pins.relative_to(area)),
                    'snapshot': str(copied.relative_to(area)), 'source': str(source),
                    'bytes': len(data), 'sha256': digest(data), 'first': first, 'last': last})
            else:
                for item in value.values():
                    visit(item)
    visit(json.loads(pins.read_text()))

modules = json.loads((area / 'modules.json').read_text())
checks = ['strict-partial-3', 'strict-oracle-4', 'strict-restart-2',
    'strict-continuation-1', 'strict-completion-2', 'strict-audit-1']
for module, check in zip(modules + ['Audit'], checks, strict=True):
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

(area / 'source-validation.json').write_text(json.dumps({'status': 'pass',
    'review_records': records, 'strict_checks': checks, 'unchanged_global_theorems': 2,
    'no_haskell_changes': True, 'audit_only_adds_imports': True}, indent=2) + '\n')
print(json.dumps({'status': 'pass', 'review_records': len(records), 'strict_checks': len(checks)}))
