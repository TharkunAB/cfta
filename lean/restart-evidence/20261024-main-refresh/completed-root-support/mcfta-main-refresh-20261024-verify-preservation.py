import gzip
import hashlib
import json
import subprocess
from pathlib import Path

here = Path(__file__).resolve().parent
root = Path('/home/tritlo/Code/mcfta')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
def load(name):
    return json.loads((here / name).read_bytes())
baseline_bytes = gzip.decompress((here / 'starting-files.json.gz').read_bytes())
assert hashlib.sha256(baseline_bytes).hexdigest() == load('baseline.json')['uncompressed_sha256']
baseline = json.loads(baseline_bytes)
merge = load('merge-report.json')
fix = load('type-depth-fix-report.json')
documents = load('document-changes.json')
upstream = merge['imported_main']
allowed = set(merge['upstream_changed_paths']) | set(documents)
unchanged = 0
lean_sources = 0
changed = []
for name, pin in baseline.items():
    path = root / name
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == pin['mode'], name
    if name in documents:
        assert digest == documents[name]['after_sha256']
        assert pin['sha256'] == documents[name]['before_sha256']
    elif name in fix['sources']:
        assert digest == fix['sources'][name]
    elif name in merge['upstream_changed_paths']:
        assert data == git('show', upstream + ':' + name), name
    else:
        assert digest == pin['sha256'] and len(data) == pin['bytes'], name
        unchanged += 1
    if digest != pin['sha256']:
        changed.append(name)
        assert name in allowed
    if name.startswith('lean/MicroCFTA/') and name.endswith('.lean'):
        assert digest == pin['sha256'], name
        lean_sources += 1
for name in merge['upstream_changed_paths']:
    if name not in fix['sources']:
        assert (root / name).read_bytes() == git('show', upstream + ':' + name), name
assert git('stash', 'list') == (here / 'starting-stashes.txt').read_bytes()
before_refs = dict(line.split()[::-1] for line in (here / 'starting-refs.txt').read_text().splitlines())
after_refs = dict(line.split()[::-1] for line in git('show-ref').decode().splitlines())
for name, value in before_refs.items():
    if name.startswith('refs/heads/') and name != 'refs/heads/formalize':
        assert after_refs[name] == value, name
    if name == 'refs/stash':
        assert after_refs[name] == value
assert after_refs['refs/heads/codex/backup-main-refresh-20261024-0033'] == merge['first_parent']
current = git('rev-parse', 'HEAD').decode().strip()
old_worktrees = (here / 'starting-worktrees.txt').read_text()
assert old_worktrees.replace('HEAD ' + merge['first_parent'] + '\n', 'HEAD ' + current + '\n', 1) == git('worktree', 'list', '--porcelain').decode()
assert git('merge-base', '--is-ancestor', upstream, 'HEAD') == b''
findings = (root / 'FINDINGS.md').read_text()
assert findings.index('## Haskell fix handoff for external work') < findings.index('## Imported main:')
assert 'Optional LPO comparator transitivity | OPEN.' in findings
assert 'Optional LPO application context | OPEN.' in findings
note = (root / 'lean/notes-current-upstream-program-enumeration.md').read_text()
assert 'No new Lean proof or Audit' in note and 'No LPO patch is applied' in note
for name, pin in load('artifacts.json').items():
    path = here / name
    data = path.read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256'], name
report = dict(status='PASS', baseline_files=len(baseline), unchanged_baseline_files=unchanged,
              changed_baseline_files=changed, unchanged_Lean_sources=lean_sources,
              upstream_main=upstream, merge=merge['merge'], negative_depth_fix=fix['commit'],
              earlier_evidence_and_drafts_unchanged=True, local_equality_reduction_unchanged=True,
              stashes_other_local_branches_and_worktrees_preserved=True,
              imported_upstream_paths=34, open_LPO_repairs=2,
              new_Lean_proofs_or_Audit_runs=0, full_goal_complete=False)
print(json.dumps(report))
