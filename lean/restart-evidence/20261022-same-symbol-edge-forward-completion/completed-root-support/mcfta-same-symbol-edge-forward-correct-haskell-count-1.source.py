import difflib
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
baseline = json.loads((HERE / 'starting-files.json').read_text())
previous = json.loads((ROOT / 'lean/restart-evidence/20261021-same-symbol-edge-control/starting-files.json').read_text())
haskell = {name for name in baseline if name.endswith('.hs')}
old_haskell = {name for name in previous if name.endswith('.hs')}
tracked = set(subprocess.check_output(['git', 'ls-files'], cwd=ROOT, text=True).splitlines())
assert len(haskell) == 292 and len(old_haskell) == 268
assert haskell == {name for name in tracked if name.endswith('.hs')}
assert old_haskell <= haskell and len(haskell - old_haskell) == 24
assert all(name.startswith('lean/restart-evidence/20261021-same-symbol-edge-control/') for name in haskell - old_haskell)
old_update = (HERE / 'current-update.md').read_text()
assert old_update == (HERE / 'findings-update.md').read_text()
assert old_update.count('All 268 Haskell') == 1
new_update = old_update.replace('All 268 Haskell', 'All 292 Haskell', 1)
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in documents:
    before = (ROOT / name).read_text()
    assert before.count(old_update) == 1
    changes[ROOT / name] = (before, before.replace(old_update, new_update, 1))
for name in ['current-update.md', 'findings-update.md']:
    changes[HERE / name] = (old_update, new_update)
path = ROOT / 'lean/notes-current-same-symbol-edge-forward-completion.md'
before = path.read_text()
assert before.count('All 268 Haskell') == 1
changes[path] = (before, before.replace('All 268 Haskell', 'All 292 Haskell', 1))
path = HERE / 'verify-preservation.py'
before = path.read_text()
old_assertion = 'assert len(hs) == 268 and len(active) == 207'
assert before.count(old_assertion) == 1
changes[path] = (before, before.replace(old_assertion, 'assert len(hs) == 292 and len(active) == 207', 1))
path = HERE / 'update-documents.py'
before = path.read_text()
assert before.count('All 268 Haskell') == 2
changes[path] = (before, before.replace('All 268 Haskell', 'All 292 Haskell'))
archive = HERE / 'haskell-count-correction'
assert not archive.exists()
archive.mkdir()
patches, pins = [], {}
for path, (before, after) in changes.items():
    name = str(path.relative_to(ROOT))
    saved = archive / 'originals' / name
    saved.parent.mkdir(parents=True, exist_ok=True)
    saved.write_text(before)
    patches.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile=name, tofile=name))
    pins[name] = {'before': hashlib.sha256(before.encode()).hexdigest(), 'after': hashlib.sha256(after.encode()).hexdigest()}
for name in ['preservation-final.stderr', 'proof-verification-normal.stdout', 'proof-verification-normal.stderr',
             'proof-verification-live.stdout', 'proof-verification-live.stderr']:
    shutil.copyfile(HERE / name, archive / name)
(archive / 'count-only.patch').write_text(''.join(patches))
(archive / 'counts.json').write_text(json.dumps({'previous_haskell': len(old_haskell), 'baseline_haskell': len(haskell),
    'added_source_copies': sorted(haskell - old_haskell), 'changed_files': pins}, indent=2) + '\n')
for path, (before, after) in changes.items():
    assert path.read_text() == before
    path.write_text(after)
print(json.dumps({'status': 'PASS', 'baseline_haskell': len(haskell), 'updated_files': len(changes)}))
