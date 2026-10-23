import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
out = Path('/tmp/mcfta-main-refresh-20261024')
start = 'd501c53489b4ba9a41fd178c7ccdd0bf530dcde7'
upstream = '6b62b4afefca80bb05f5a37546212a99980aa3df'
prior = '794903b3fbad3becb8b28736fc33463760731fc7'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', 'HEAD').decode().strip() == start
assert git('rev-parse', 'origin/main').decode().strip() == upstream
assert not git('status', '--porcelain')
assert git('merge-base', start, upstream).decode().strip() == prior
changed = set(git('diff', '--name-only', prior, upstream).decode().splitlines())
assert len(changed) == 34
assert not any(name.startswith('lean/') or name in ['FINDINGS.md', 'HANDOFF.md', 'NEXT-PROMPT.md'] for name in changed)
result = subprocess.run(['git', 'merge', '--no-ff', '--no-commit', upstream],
                        cwd=root, capture_output=True)
(out / 'merge.log').write_bytes(result.stdout + result.stderr)
assert result.returncode == 0, (result.stdout + result.stderr).decode()
assert not git('diff', '--name-only', '--diff-filter=U')
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == changed
baseline = json.loads((out / 'starting-files.json').read_text())
unchanged = 0
for name, pin in baseline.items():
    if name in changed:
        continue
    path = root / name
    data = path.read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256'], name
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == pin['mode'], name
    unchanged += 1
for name in changed:
    assert (root / name).read_bytes() == git('show', upstream + ':' + name), name
assert git('stash', 'list') == (out / 'starting-stashes.txt').read_bytes()
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Merge main program enumeration and template refinement updates'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
assert git('rev-list', '--parents', '-n', '1', head).decode().split() == [head, start, upstream]
assert not git('status', '--porcelain')
report = dict(status='PASS', merge=head, first_parent=start, imported_main=upstream,
              prior_imported_main=prior, upstream_changed_paths=sorted(changed),
              baseline_files=len(baseline), baseline_files_unchanged=unchanged,
              every_upstream_path_byte_identical=True, all_Lean_and_evidence_unchanged=True,
              local_equality_operations_retained=True, stashes_unchanged=True,
              clean=True, semantic_evaluation_and_tests='PENDING')
(out / 'merge-report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({key: value for key, value in report.items() if key != 'upstream_changed_paths'}))
