from pathlib import Path
import hashlib
import json
import subprocess

area = Path('/tmp/mcfta-flat-native-fold-20261027')
counts = {'files': 0, 'cuts': 0, 'git_blobs': 0}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def visit(value):
    if isinstance(value, list):
        for item in value:
            visit(item)
    elif isinstance(value, dict):
        source = value.get('source', value.get('path', value.get('original')))
        if source and 'sha256' in value:
            if 'commit' in value:
                original = subprocess.check_output(['git', 'show', value['commit'] + ':' + source], cwd='/home/tritlo/Code/mcfta')
                counts['git_blobs'] += 1
            else:
                original = Path(source).read_bytes()
            standalone_cut = 'first' in value and 'last' in value
            if standalone_cut:
                original = b''.join(original.splitlines(keepends=True)[value['first'] - 1:value['last']])
            snapshot = value.get('snapshot', value.get('reviewed_copy'))
            if snapshot:
                assert original == Path(snapshot).read_bytes(), source
            if 'bytes' in value:
                assert len(original) == value['bytes'], source
            assert digest(original) == value['sha256'], source
            counts['cuts' if standalone_cut else 'files'] += 1
            for cut in value.get('cuts', []) + value.get('focused_spans', []):
                first = cut.get('first', cut.get('first_line'))
                last = cut.get('last', cut.get('last_line'))
                data = b''.join(original.splitlines(keepends=True)[first - 1:last])
                if 'snapshot' in cut:
                    assert data == Path(cut['snapshot']).read_bytes(), cut
                assert len(data) == cut['bytes'] and digest(data) == cut['sha256'], cut
                counts['cuts'] += 1
            prefix = value.get('reviewed_prefix_copy')
            if prefix:
                data = b''.join(original.splitlines(keepends=True)
                    [prefix['first_line'] - 1:prefix['last_line']])
                assert data == Path(prefix['path']).read_bytes(), prefix
                assert len(data) == prefix['bytes'] and digest(data) == prefix['sha256'], prefix
                counts['cuts'] += 1
        for item in value.values():
            if isinstance(item, (dict, list)):
                visit(item)

pins = sorted(area.glob('*review/source-pins.json'))
assert len(pins) == 5, pins
for pin in pins:
    visit(json.loads(pin.read_text()))
report = dict(counts, pin_files=[str(pin.relative_to(area)) for pin in pins], result='pass')
(area / 'review-pin-validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
