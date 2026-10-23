import gzip, hashlib, json, subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-enumerate-until-20261024')
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
def sha(data):
    return hashlib.sha256(data).hexdigest()

baseline = json.loads(gzip.decompress((area/'starting-files.json.gz').read_bytes()))
changes = json.loads((area/'document-changes.json').read_text())
allowed = set(changes) | {'lean/MicroCFTA/Audit.lean'}
changed = []
lean_count = 0
haskell_count = 0
for name, entry in baseline.items():
    path = root/name
    data = path.read_bytes()
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == entry['mode'], name
    lean_count += name.startswith('lean/MicroCFTA/') and name.endswith('.lean')
    haskell_count += name.endswith('.hs')
    if sha(data) != entry['sha256']:
        assert name in allowed, name
        changed.append(name)
        if name == 'lean/MicroCFTA/Audit.lean':
            prefix = b'import MicroCFTA.EnumerationUntilBridge\n'
            assert data.startswith(prefix) and sha(data[len(prefix):]) == entry['sha256']
        else:
            change = changes[name]
            text = data.decode()
            index = change['insertion_character']
            addition = change['inserted']
            assert text[index:index+len(addition)] == addition
            original = (text[:index]+text[index+len(addition):]).encode()
            assert sha(original) == entry['sha256'] == change['before_sha256']
            assert sha(data) == change['after_sha256']
assert set(changed) == allowed
start = (area/'starting-head.txt').read_text().strip()
head = git('rev-parse', 'HEAD').decode().strip()
assert head == 'ecabbf38e669d96275ce991fa8a843bcec3b51ed'
assert git('branch', '--show-current').decode().strip() == 'formalize'
subprocess.run(['git', 'merge-base', '--is-ancestor', start, head], cwd=root, check=True)
assert git('stash', 'list') == (area/'starting-stashes.txt').read_bytes()
trees = (area/'starting-worktrees.txt').read_text().replace('HEAD '+start, 'HEAD '+head, 1)
assert git('worktree', 'list', '--porcelain').decode() == trees
refs = {line.split()[1]:line.split()[0] for line in git('show-ref').decode().splitlines()}
for line in (area/'starting-refs.txt').read_text().splitlines():
    commit, ref = line.split()
    if ref.startswith('refs/heads/') and ref != 'refs/heads/formalize':
        assert refs[ref] == commit, ref
assert refs['refs/heads/codex/backup-enumerate-until-20261024-0055'] == start
assert refs['refs/remotes/origin/main'] == '6b62b4afefca80bb05f5a37546212a99980aa3df'
findings = (root/'FINDINGS.md').read_text()
assert findings.index('## Haskell fix handoff for external work') < findings.index('## Shared enumeration:')
report = dict(status='PASS', baseline_files=len(baseline), unchanged_files=len(baseline)-len(changed),
              changed_with_exact_preserved_suffix=sorted(changed), baseline_lean_sources=lean_count,
              baseline_haskell_sources=haskell_count, all_haskell_unchanged=True,
              older_lean_bodies_unchanged=True, earlier_evidence_unchanged=True,
              stashes_and_other_local_branches_and_worktrees_preserved=True,
              start=start, proof_commit=head, goal='ACTIVE_INCOMPLETE')
(area/'preservation.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
