import difflib
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = (HERE / 'same-symbol-edge-stable-strict-3.source.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'f665ea5c2b6a36cd583796b87e51b563106a5c536a9274cfbe7b633b6d05dc93'
assert json.loads((HERE / 'same-symbol-edge-stable-strict-3.json').read_text())['exit_code'] == 0
old = '  · subst handle; simp [put, different]\n'.encode()
new = old.replace(b', different', b'')
assert source.count(old) == 1
selected = source.replace(old, new, 1)
target = Path('/tmp/mcfta-same-symbol-edge-stable-root-v5')
assert not target.exists()
target.mkdir()
(target / 'SourceCurrentSameSymbolEdgeStable.lean').write_bytes(selected)
(target / 'unused-argument.patch').write_text(''.join(difflib.unified_diff(source.decode().splitlines(keepends=True), selected.decode().splitlines(keepends=True), fromfile='warned-strict-3.source.lean', tofile='selected-v5.source.lean')))
saved = target / 'warned-strict-3'
saved.mkdir()
for suffix in ['source.lean', 'log', 'json', 'limits.json', 'usage.json']:
    original = HERE / ('same-symbol-edge-stable-strict-3.' + suffix)
    shutil.copyfile(original, saved / original.name)
(target / 'note.md').write_text('SOURCE-ONLY LINTER REPAIR; UNCOMPILED.\nThe third strict check exited zero with one unused-simp warning.\nThe exact patch removes only the unused different argument at finish_two.\nEvery declaration type and all public contract bytes remain unchanged.\nThe warned input, complete log and owned receipts remain unchanged.\nNo linter or declaration limit changes. This preparation runs no Lean.\n')
pins = {str(path.relative_to(target)): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(target.rglob('*')) if path.is_file()}
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'SOURCE_ONLY', 'source_lines': len(selected.splitlines()), 'source_sha256': hashlib.sha256(selected).hexdigest()}))
