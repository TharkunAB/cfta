"""Verify the upstream merge and the exact document changes without a compiler."""
import hashlib
import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[3]
here = Path(__file__).resolve().parent
baseline = 'c841846eba7ab893460375a99a34e1d3f27ee9b0'
merge = '65f237954c3e867570c06d2de22681f55ca64fcd'
main = 'a5fbb66eec52b8c28a4beacd982f00626c9e279a'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)

def sha(data):
    return hashlib.sha256(data).hexdigest()

assert git('branch', '--show-current').decode().strip() == 'formalize'
subprocess.run(['git', 'merge-base', '--is-ancestor', main, 'HEAD'], cwd=root, check=True)
assert git('rev-parse', baseline + '^{tree}') == git('rev-parse', merge + '^{tree}')
assert not git('diff', baseline, merge)
changes = json.loads((here / 'document-changes.json').read_text())
repair = json.loads((here / 'finding-status-change.json').read_text())
changed = []
count = 0
lean_sources = 0
haskell_sources = 0
for raw in git('ls-tree', '-r', '-z', baseline).split(b'\0'):
    if not raw:
        continue
    metadata, raw_name = raw.split(b'\t', 1)
    mode, kind, blob = metadata.decode().split()
    name = raw_name.decode()
    path = root / name
    assert kind == 'blob'
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
    data = path.read_bytes()
    if name in changes:
        changed.append(name)
        change = changes[name]
        assert sha(data) == change['after_sha256'], name
        text = data.decode()
        index, inserted = change['insertion_character'], change['inserted']
        assert text[index:index + len(inserted)] == inserted, name
        data = (text[:index] + text[index + len(inserted):]).encode()
        assert sha(data) == change['before_sha256'], name
    if name == 'FINDINGS.md':
        assert sha(data) == repair['after_sha256']
        text = data.decode()
        for before, after in repair['replacements']:
            assert text.count(after) == 1
            text = text.replace(after, before, 1)
        data = text.encode()
        assert sha(data) == repair['before_sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    count += 1
    lean_sources += name.endswith('.lean')
    haskell_sources += name.endswith(('.hs', '.lhs'))
assert len(changed) == len(changes) == 9
assert git('stash', 'list') == (here / 'starting-stashes.txt').read_bytes()
worktrees = (here / 'starting-worktrees.txt').read_bytes()
live_head = git('rev-parse', 'HEAD').strip()
assert git('worktree', 'list', '--porcelain') == worktrees.replace(b'HEAD ' + baseline.encode(), b'HEAD ' + live_head, 1)
findings = (root / 'FINDINGS.md').read_text()
assert findings.index('## Haskell fix handoff for external work') < findings.index('## Current main incorporated')
report = dict(status='PASS', baseline=baseline, main=main, merge=merge,
              baseline_files=count, unchanged_files=count - len(changed),
              lean_sources_preserved=lean_sources, haskell_sources_preserved=haskell_sources,
              exact_document_updates=changed, implementation_changes=0,
              compiler_jobs=0, goal='ACTIVE_INCOMPLETE')
print(json.dumps(report, indent=2))
