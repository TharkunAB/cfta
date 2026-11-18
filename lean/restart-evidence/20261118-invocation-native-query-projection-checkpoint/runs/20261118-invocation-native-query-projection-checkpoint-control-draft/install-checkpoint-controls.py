from pathlib import Path
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
DRAFT = Path(__file__).resolve().parent
WORK = ROOT / 'lean/restart-evidence/20261118-invocation-native-query-projection-work'
NAMES = ['prepare-checkpoint-controls.py', 'assemble.py', 'finalize.py', 'verify.py', 'commit-checkpoint.py', 'selection-roots.json', 'prior-bindings.json', 'original-header-files.json', 'archive-additional-roots.json', 'checkpoint-note.md', 'HISTORICAL-OVERRIDES.json', 'COMPONENTS.json']
manifest = json.loads((DRAFT / 'MANIFEST.json').read_text())
assert manifest['status'] == 'FROZEN CANDIDATE / NOT EXECUTED'
for name, item in manifest['files'].items():
    data = (DRAFT / name).read_bytes()
    assert len(data) == item['bytes']
    assert hashlib.sha256(data).hexdigest() == item['sha256'], name
assert WORK.is_dir() and DRAFT != WORK
for name in NAMES:
    target = WORK / name
    assert not target.is_symlink()
    assert not target.exists() or target.read_bytes() == (DRAFT / name).read_bytes(), name
for name in NAMES:
    target = WORK / name
    if not target.exists():
        target.write_bytes((DRAFT / name).read_bytes())
print(json.dumps({'installed': NAMES, 'work': str(WORK), 'controllers_executed': False}))
