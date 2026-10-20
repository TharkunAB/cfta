import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
IMPORTED_MAIN = '794903b3fbad3becb8b28736fc33463760731fc7'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


baseline = json.loads((HERE / 'starting-sha256.json').read_text())
assert len(baseline) == 45220
documents = json.loads((HERE / 'current-documents.json').read_text())
upstream_files = {'cfta-generator/CHANGELOG.md', 'cfta-generator/README.md',
                  'cfta-generator/src/Data/CFTA/Gen/Typing.hs'}
old_documents = {name for name in documents if name in baseline}
assert len(old_documents) == 9
assert not [name for name in baseline if not (ROOT / name).is_file()]
changed = {name for name, expected in baseline.items() if sha(ROOT / name) != expected}
assert changed == upstream_files | old_documents, sorted(changed ^ (upstream_files | old_documents))
for name in upstream_files:
    assert (ROOT / name).read_bytes() == subprocess.check_output(['git', 'show', IMPORTED_MAIN + ':' + name], cwd=ROOT)
old_head = (HERE / 'starting-head.txt').read_text().strip()
typing = 'cfta-generator/src/Data/CFTA/Gen/Typing.hs'
old_typing = git('show', old_head + ':' + typing)
new_typing = (ROOT / typing).read_text()
without_haddock = lambda text: re.sub(r'\{- \|.*?-\}', '', text, flags=re.S)
assert without_haddock(old_typing) == without_haddock(new_typing)
assert not subprocess.run(['git', 'merge-base', '--is-ancestor', IMPORTED_MAIN, 'HEAD'], cwd=ROOT).returncode
merge = json.loads((HERE / 'merge.json').read_text())
assert merge['exit_code'] == 0 and merge['main'] == IMPORTED_MAIN
assert not subprocess.run(['git', 'merge-base', '--is-ancestor', merge['head'], 'HEAD'], cwd=ROOT).returncode
assert git('branch', '--show-current').strip() == 'formalize'
assert git('stash', 'list', '--format=%gd %H %s') == (HERE / 'starting-stashes.txt').read_text()
other = lambda text: [block for block in text.strip().split('\n\n') if not block.startswith(f'worktree {ROOT}\n')]
assert other(git('worktree', 'list', '--porcelain')) == other((HERE / 'starting-worktrees.txt').read_text())
current = set(git('ls-files').splitlines())
haskell = {name for name in baseline if name.endswith('.hs')}
packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
package_files = {name for name in baseline if name.split('/', 1)[0] in packages}
lean = {name for name in baseline if name.startswith('lean/MicroCFTA/') and name.endswith('.lean')}
assert haskell == {name for name in current if name.endswith('.hs')}
assert package_files == {name for name in current if name.split('/', 1)[0] in packages}
assert not lean & changed
assert len(haskell) == 268 and len(package_files) == 207 and len(lean) == 3534
prior = ROOT / 'lean/restart-evidence/20261020-native-original-union-descent'
frozen = json.loads((prior / 'preservation-final.json').read_text())['frozen_manifests']
entries = 0
for name, metadata in frozen.items():
    assert sha(ROOT / name) == metadata['manifest_sha256']
    modules = json.loads((ROOT / name).read_text())
    for module, expected in modules.items():
        source = module if '/' in module else 'lean/MicroCFTA/' + module + '.lean'
        assert sha(ROOT / source) == expected
    entries += len(modules)
assert len(frozen) == 220 and entries == 1291
finding = (ROOT / 'FINDINGS.md').read_text()
assert finding.startswith('# Current formalization findings\n\n## Haskell fix handoff for external work\n\n')
assert finding.replace((HERE / 'findings-update.md').read_text(), '', 1) == git('show', old_head + ':FINDINGS.md')
proof = json.loads(subprocess.check_output([sys.executable, str(prior / 'verify-checkpoint.py')],
                                         cwd='/', env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}))
assert proof['status'] == 'PASS' and proof['proof_commit'] == '0b533a71852046e391dbed6e1c5761189465fa90'
assert proof['audit_jobs'] == 3536 and proof['audit_dependency_checks'] == 74283
print(json.dumps({'status': 'PASS', 'imported_main': IMPORTED_MAIN, 'merge': merge['head'],
                  'baseline_files': len(baseline), 'changed': sorted(changed),
                  'all_lean_sources_unchanged': len(lean), 'older_non_audit_sources_unchanged': len(lean) - 1,
                  'haskell_files': len(haskell), 'unchanged_haskell_files': len(haskell) - 1,
                  'typing_outside_haddock_unchanged': True, 'active_package_files': len(package_files),
                  'upstream_files_match_exactly': sorted(upstream_files), 'frozen_manifests': len(frozen),
                  'frozen_entries': entries, 'stashes': 2, 'other_worktrees': 3,
                  'selected_proof_evidence': proof, 'new_lean_jobs': 0}, indent=2))
