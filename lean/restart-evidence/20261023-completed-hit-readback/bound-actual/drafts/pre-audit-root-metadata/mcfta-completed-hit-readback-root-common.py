import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-completed-hit-readback'
NAME = 'SourceCurrentSameSymbolEdgeHitReadback'
START = 'd8503f911255e53beb8904dacd7d978349ec7887'

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
    for pin in entries:
        relative = Path(pin['path'])
        assert not relative.is_absolute() and '..' not in relative.parts
        item = path / relative
        assert item.stat().st_size == pin['bytes'] and sha(item) == pin['sha256'], item
    return entries

def archive(path, name):
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(path), name], check=True)

def save(name, data):
    path = HERE / name
    assert not path.exists(), path
    path.write_text(json.dumps(data, indent=2) + '\n')

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
