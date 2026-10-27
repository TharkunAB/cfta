from pathlib import Path
import hashlib
import json

area = Path('/tmp/mcfta-flat-native-index-20261027')
counts = {'files': 0, 'cuts': 0}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def visit(value):
    if isinstance(value, list):
        for item in value:
            visit(item)
    elif isinstance(value, dict):
        source = value.get('source', value.get('path', value.get('original')))
        if source and 'snapshot' in value and 'sha256' in value:
            original = Path(source).read_bytes()
            snapshot = Path(value['snapshot']).read_bytes()
            assert original == snapshot, source
            assert len(original) == value['bytes'], source
            assert digest(original) == value['sha256'], source
            counts['files'] += 1
            for cut in value.get('cuts', []):
                data = b''.join(original.splitlines(keepends=True)[cut['first'] - 1:cut['last']])
                assert data == Path(cut['snapshot']).read_bytes(), cut
                assert len(data) == cut['bytes'] and digest(data) == cut['sha256'], cut
                counts['cuts'] += 1
        for item in value.values():
            if isinstance(item, (dict, list)):
                visit(item)

pins = sorted(area.glob('*review/*pins*.json'))
assert len(pins) == 3, pins
for pin in pins:
    visit(json.loads(pin.read_text()))
report = dict(counts, pin_files=[str(pin.relative_to(area)) for pin in pins], result='pass')
(area / 'review-pin-validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
