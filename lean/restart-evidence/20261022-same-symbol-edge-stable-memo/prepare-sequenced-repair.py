import difflib
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = (HERE / 'same-symbol-edge-stable-strict-2.source.lean').read_text()
assert hashlib.sha256(source.encode()).hexdigest() == '35a92ce3bd517baeeccf0df68acf5ed1c7f87eb98e351f59b649cf5fa6777e7b'
repairs = [
    ('    simp only [FlatMemoThunk.setStatus, stored, published, FlatMemoThunk.lookupOrInsert, missing, started, overwrite_cells]',
     '    simp only [FlatMemoThunk.setStatus, stored]\n    simp only [published, FlatMemoThunk.lookupOrInsert, missing, started, overwrite_cells]'),
    ('  simp only [FlatMemoThunk.finish, stored, FlatMemoThunk.setStatus, started, written, overwrite_cells]',
     '  simp only [FlatMemoThunk.finish, stored]\n  simp only [FlatMemoThunk.setStatus, stored]\n  simp only [started, written, overwrite_cells]'),
    ('  rw [finish_started (right, left) value (started (left, right) memo)]',
     '  have inner : FlatMemoThunk.finish (memo.next + 1) value (started (right, left) (started (left, right) memo)) =\n      written (right, left) value (started (left, right) memo) :=\n    finish_started (right, left) value (started (left, right) memo)\n  rw [inner]'),
    ('  simp only [FlatMemoThunk.finish, stored, FlatMemoThunk.setStatus, written, started]',
     '  simp only [FlatMemoThunk.finish, stored]\n  simp only [FlatMemoThunk.setStatus, stored]\n  simp only [written, started]'),
    ('  · simpa only [FlatMemoThunk.setStatus, stored, published, FlatMemoThunk.lookupOrInsert, missing, written, overwrite_cells] using changed',
     '  · simp only [FlatMemoThunk.setStatus, stored] at changed\n    simpa only [published, FlatMemoThunk.lookupOrInsert, missing, written, overwrite_cells] using changed'),
]
selected = source
for old, new in repairs:
    assert selected.count(old) == 1
    selected = selected.replace(old, new, 1)
assert len(selected.splitlines()) <= 350
prefix = source[:source.index('private theorem tail_done ')]
assert selected.startswith(prefix)
header = lambda text: text[text.index('theorem completed_preserves '):text.index(' := by', text.index('theorem completed_preserves '))]
assert header(selected) == header(source)
target = Path('/tmp/mcfta-same-symbol-edge-stable-root-v4')
assert not target.exists()
target.mkdir()
name = 'SourceCurrentSameSymbolEdgeStable.lean'
(target / name).write_text(selected)
(target / 'sequenced-rewrite.patch').write_text(''.join(difflib.unified_diff(source.splitlines(keepends=True), selected.splitlines(keepends=True), fromfile='failed-strict-2.source.lean', tofile='selected-v4.source.lean')))
failed = target / 'failed-strict-2'
failed.mkdir()
for suffix in ['source.lean', 'log', 'json', 'limits.json', 'usage.json']:
    original = HERE / ('same-symbol-edge-stable-strict-2.' + suffix)
    shutil.copyfile(original, failed / original.name)
(target / 'note.md').write_text('SOURCE-ONLY ROOT REPAIR; UNCOMPILED.\nThe patch sequences stored-cell rewrites before record unfolding at four proof sites.\nAn explicit inner-finish equation normalizes its next projection before rewrite.\nThe context, documented Stable, helper declarations and public theorem header remain unchanged.\nThe previous complete source and failed strict2 artifacts remain byte-exact.\nNo linter or declaration limit changes. No compiler or proof checker runs here.\nIndependent source review is required before another ordinary check.\n')
pins = {str(path.relative_to(target)): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(target.rglob('*')) if path.is_file()}
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({'status': 'SOURCE_ONLY', 'source_lines': len(selected.splitlines()), 'source_sha256': pins[name], 'repair_sites': len(repairs)}))
