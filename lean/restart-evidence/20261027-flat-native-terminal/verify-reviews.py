from pathlib import Path
import hashlib
import json
import subprocess

area = Path('/tmp/mcfta-flat-native-terminal-20261027')
counts = {'files': 0, 'cuts': 0, 'git_blobs': 0, 'snapshot_only': 0}
pin_root = area

def resolve(name):
    path = Path(name)
    return path if path.is_absolute() else pin_root / path

def digest(data):
    return hashlib.sha256(data).hexdigest()

def visit(value):
    if isinstance(value, list):
        for item in value:
            visit(item)
    elif isinstance(value, dict):
        source = value.get('source', value.get('source_path', value.get('path', value.get('original'))))
        if source and 'sha256' in value:
            if 'commit' in value:
                original = subprocess.check_output(['git', 'show', value['commit'] + ':' + source], cwd='/home/tritlo/Code/mcfta')
                counts['git_blobs'] += 1
            else:
                original = resolve(source).read_bytes()
            for whole_key in ['source_sha256', 'whole_sha256']:
                if whole_key in value:
                    assert digest(original) == value[whole_key], source
            first = value.get('first', value.get('first_line'))
            last = value.get('last', value.get('last_line'))
            standalone_cut = first is not None and last is not None
            if standalone_cut:
                original = b''.join(original.splitlines(keepends=True)[first - 1:last])
            snapshot = value.get('snapshot', value.get('copy_path', value.get('reviewed_copy')))
            if snapshot:
                assert original == resolve(snapshot).read_bytes(), source
            if 'bytes' in value:
                assert len(original) == value['bytes'], source
            assert digest(original) == value['sha256'], source
            counts['cuts' if standalone_cut else 'files'] += 1
            for cut in value.get('cuts', []) + value.get('focused_spans', []):
                first = cut.get('first', cut.get('first_line'))
                last = cut.get('last', cut.get('last_line'))
                data = b''.join(original.splitlines(keepends=True)[first - 1:last])
                if 'snapshot' in cut:
                    assert data == resolve(cut['snapshot']).read_bytes(), cut
                assert len(data) == cut['bytes'] and digest(data) == cut['sha256'], cut
                counts['cuts'] += 1
        elif 'snapshot' in value and 'sha256' in value:
            data = resolve(value['snapshot']).read_bytes()
            assert len(data) == value['bytes'] and digest(data) == value['sha256'], value
            counts['snapshot_only'] += 1
            prefix = value.get('reviewed_prefix_copy')
            if prefix:
                data = b''.join(original.splitlines(keepends=True)
                    [prefix['first_line'] - 1:prefix['last_line']])
                assert data == resolve(prefix['path']).read_bytes(), prefix
                assert len(data) == prefix['bytes'] and digest(data) == prefix['sha256'], prefix
                counts['cuts'] += 1
        for item in value.values():
            if isinstance(item, (dict, list)):
                visit(item)

pins = sorted(area.glob('*review/source-pins.json'))
assert 7 <= len(pins) <= 9, pins
for pin in pins:
    pin_root = pin.parent
    visit(json.loads(pin.read_text()))
report = dict(counts, pin_files=[str(pin.relative_to(area)) for pin in pins], result='pass')
(area / 'review-pin-validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
