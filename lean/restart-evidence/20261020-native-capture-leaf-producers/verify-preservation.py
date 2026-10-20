import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)


def others(data):
    return [block for block in data.strip().split('\n\n')
            if not block.startswith(f'worktree {ROOT}\n')]


baseline = json.loads((HERE / 'starting-sha256.json').read_text())
missing = [name for name in baseline if not (ROOT / name).is_file()]
changed = [name for name, expected in baseline.items()
           if (ROOT / name).is_file() and sha(ROOT / name) != expected]
allowed = {
    'NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/MicroCFTA/Audit.lean', 'lean/notes-proof-status-20261017.md',
    'lean/notes-current-system-claim.md',
}
assert not missing, missing
assert set(changed) == allowed, sorted(set(changed) ^ allowed)
head = (HERE / 'starting-head.txt').read_text().strip()
prior = git('show', head + ':lean/MicroCFTA/Audit.lean')
names = json.loads((HERE / 'new-modules.json').read_text())
imports = ''.join('import MicroCFTA.' + name + '\n' for name in names)
anchor = 'import MicroCFTA.SourceCurrentNativeCapturedMuOrigins\n'
assert prior.count(anchor) == 1
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_text() == prior.replace(anchor, anchor + imports, 1)
previous = json.loads((ROOT / 'lean/restart-evidence/20261020-native-active-result-lineage/preservation-final.json').read_text())
manifest_paths = list(previous['frozen_manifests']) + [str((HERE / 'frozen-modules.json').relative_to(ROOT))]
frozen = {}
for name in manifest_paths:
    entries = json.loads((ROOT / name).read_text())
    for module, expected in entries.items():
        source = module if '/' in module else 'lean/MicroCFTA/' + module + '.lean'
        assert sha(ROOT / source) == expected, (name, source)
    frozen[name] = {'checked': len(entries), 'manifest_sha256': sha(ROOT / name)}
upstream = json.loads((HERE / 'upstream-refresh.json').read_text())
assert upstream['pull_exit_code'] == 0 and not upstream['this_checkpoint_imported_changes']
assert git('rev-parse', 'origin/main').strip() == upstream['main']
assert not subprocess.run(['git', 'merge-base', '--is-ancestor', upstream['main'], 'HEAD'], cwd=ROOT).returncode
assert git('stash', 'list', '--format=%gd %H %s') == (HERE / 'starting-stashes.txt').read_text()
assert git('stash', 'list', '--format=%gd %H %s') == (ROOT / 'lean/restart-evidence/20261019-recursive-value-ancestry/starting-stashes.txt').read_text()
assert others(git('worktree', 'list', '--porcelain')) == others((HERE / 'starting-worktrees.txt').read_text())
assert git('branch', '--show-current').strip() == 'formalize'
packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
package_files = {name for name in baseline if name.split('/', 1)[0] in packages}
current_files = git('ls-files').splitlines()
assert package_files == {name for name in current_files if name.split('/', 1)[0] in packages}
assert not package_files & set(changed)
haskell = {name for name in baseline if name.endswith('.hs')}
assert haskell == {name for name in current_files if name.endswith('.hs')}
assert not haskell & set(changed)
findings = (ROOT / 'FINDINGS.md').read_text()
assert findings.startswith('# Current formalization findings\n\n## Haskell fix handoff for external work\n')
assert 'b9219b9e' in findings[:findings.index('- **Negative typed-language bounds.**')]
old = git('show', head + ':FINDINGS.md')
assert findings.replace((HERE / 'findings-update.md').read_text(), '', 1) == old
report = {
    'status': 'PASS', 'baseline_files': len(baseline),
    'baseline_sha256': sha(HERE / 'starting-sha256.json'),
    'missing': missing, 'changed': sorted(changed),
    'older_non_audit_sources': sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean')
                                   and name != 'lean/MicroCFTA/Audit.lean' for name in baseline),
    'all_starting_haskell_files': len(haskell), 'all_haskell_unchanged': True,
    'active_package_files': len(package_files), 'all_active_package_files_unchanged': True,
    'upstream_main': upstream['main'], 'new_upstream_import': False,
    'audit_only_adds_declared_imports': True,
    'stashes': len((HERE / 'starting-stashes.txt').read_text().splitlines()),
    'other_worktrees': len(others(git('worktree', 'list', '--porcelain'))),
    'frozen_manifest_count': len(frozen),
    'frozen_module_entries': sum(item['checked'] for item in frozen.values()),
    'frozen_manifests': frozen, 'haskell_fix_registry_first_and_retained': True,
}
assert report['baseline_files'] == 43632
assert report['older_non_audit_sources'] == 3515
assert report['all_starting_haskell_files'] == 268
assert report['active_package_files'] == 207
assert report['frozen_manifest_count'] == 215
assert report['frozen_module_entries'] == 1273 + len(names)
print(json.dumps(report, indent=2))
