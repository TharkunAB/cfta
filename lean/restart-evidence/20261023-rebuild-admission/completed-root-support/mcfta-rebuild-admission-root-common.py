import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-rebuild-admission'
NAME = 'SourceCurrentOriginalRowRebuildAdmission'
START = '825d83243f4e69b39b2211598d92e15c427f88ed'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_bytes())

def checked_package(path, expected_pins, expected_freeze):
    assert sha(path / 'pins.json') == expected_pins
    assert sha(path / 'FROZEN.json') == expected_freeze
    entries = load(path / 'pins.json')
    if isinstance(entries, dict):
        entries = [dict(path=name, **pin) for name, pin in entries.items()]
    assert isinstance(entries, list) and entries
    listed = set()
    for pin in entries:
        relative = Path(pin['path'])
        if relative.is_absolute():
            relative = relative.relative_to(path)
        assert not relative.is_absolute() and '..' not in relative.parts
        item = path / relative
        assert item.stat().st_size == pin['bytes'] and sha(item) == pin['sha256'], item
        listed.add(str(relative))
    actual = {str(p.relative_to(path)) for p in path.rglob('*') if p.is_file()}
    assert listed == actual - {'pins.json', 'FROZEN.json'}
    return entries

def archive(path, name):
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(path), name], check=True)

def save(name, data):
    path = HERE / name
    assert not path.exists(), path
    path.write_text(json.dumps(data, indent=2) + '\n')

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
