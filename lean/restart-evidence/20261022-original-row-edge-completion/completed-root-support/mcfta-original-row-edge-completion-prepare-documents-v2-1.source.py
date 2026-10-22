import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
before = (HERE / 'checkpoint-preparation/update-documents.py').read_text()
after = before
for first, second in [
    ('language iff, recursive Mu completion or the full public pass.',
     'language iff, the public Mu unfolding and kept-body branch, or the full public pass.'),
    ('parent by payload readback. Closed opaque Mu values do not establish',
     'parent by payload readback. Closed Mu values do not establish'),
    ('cache rebasing, cluster reconstruction, recursive Mu or full',
     'cache rebasing, cluster reconstruction, the public Mu branch or full'),
]:
    assert after.count(first) == 1
    after = after.replace(first, second)
target = Path('/tmp/mcfta-original-row-edge-completion-documents-preparation-v2')
target.mkdir()
(target / 'update-documents.py').write_text(after)
(target / 'update-documents.original.py.txt').write_text(before)
(target / 'wording.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),
    after.splitlines(True), fromfile='H11-writer-1', tofile='H11-writer-2')))
(target / 'pins.json').write_text(json.dumps({path.name: hashlib.sha256(path.read_bytes()).hexdigest()
    for path in target.iterdir() if path.is_file()}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'prose_changes': 3, 'writer_not_executed': True}))
