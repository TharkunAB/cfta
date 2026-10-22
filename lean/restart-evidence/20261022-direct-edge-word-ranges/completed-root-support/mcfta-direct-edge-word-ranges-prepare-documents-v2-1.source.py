import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
original = Path('/tmp/mcfta-direct-edge-word-ranges-checkpoint-preparation/update-documents.py').read_bytes()
assert original.count(b'Code.edgeBody at the exact emptyDomain') == 1
changed = original.replace(b'Code.edgeBody at the exact emptyDomain',
                           b'Control.edgeBody at the exact emptyDomain', 1)
target = Path('/tmp/mcfta-direct-edge-word-ranges-documents-preparation-v2')
assert not target.exists()
target.mkdir()
(target / 'update-documents.original.py.txt').write_bytes(original)
(target / 'update-documents.py').write_bytes(changed)
(target / 'wording.patch').write_text(''.join(difflib.unified_diff(
    original.decode().splitlines(True), changed.decode().splitlines(True),
    fromfile='H12-original-writer', tofile='H12-writer-v2')))
(target / 'note.md').write_text('''SOURCE-ONLY writer correction.
The focused note now names Control.edgeBody, its actual declaration.
The original writer and exact one-occurrence prose delta remain.
All executable assertions and future rejecting bindings retain their bytes.
No prepared writer or proof command was executed.
The theorem scope remains WordRanges only. Remote publication is pending.
''')
pins = {str(path.relative_to(target)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(target.rglob('*')) if path.is_file()}
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'files': len(pins), 'writer_lines': len(changed.splitlines()),
                  'writer_sha256': hashlib.sha256(changed).hexdigest(), 'executed_writer': False}))
