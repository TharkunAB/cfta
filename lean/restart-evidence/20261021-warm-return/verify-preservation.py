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

base = json.loads((HERE / 'starting-files.json').read_text())
changed = []
for name, pin in base.items():
    path = ROOT / name
    assert path.is_file(), name
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == pin['mode'], name
    if sha(path) != pin['sha256']:
        changed.append(name)
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
selected = json.loads((HERE / 'selected-sources.json').read_text())
assert json.loads((HERE / 'frozen-modules.json').read_text()) == {
    Path(name).stem: pin['sha256'] for name, pin in selected.items()}
assert set(changed) == set(documents) | set(selected), changed
start = (HERE / 'starting-head.txt').read_text().strip()
for name in documents:
    update = 'findings-update.md' if name == 'FINDINGS.md' else 'current-update.md'
    assert (ROOT / name).read_text().replace((HERE / update).read_text() + '\n', '', 1) == git('show', start + ':' + name), name
marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
marker += (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n\n'
assert (ROOT / 'FINDINGS.md').read_text().startswith(marker)
previous = json.loads((HERE / 'previous-publication.json').read_text())['preservation']
archives = dict(previous['frozen_entry_archives'])
added = json.loads((HERE / 'new-frozen-entry-archives.json').read_text())
assert not set(added) & set(archives)
archives.update(added)
registries = dict(previous['frozen_manifests'])
registries['lean/restart-evidence/20261021-cold-rank-capacity/frozen-modules.json'] = {}
frozen = {}
for name in registries:
    entries = json.loads((ROOT / name).read_text())
    for module, expected in entries.items():
        source = module if '/' in module else 'lean/MicroCFTA/' + module + '.lean'
        if sha(ROOT / source) != expected:
            entry = archives[source]
            assert entry['sha256'] == expected and sha(ROOT / entry['snapshot']) == expected
            assert sha(ROOT / source) == entry['current_sha256']
    frozen[name] = {'checked': len(entries), 'manifest_sha256': sha(ROOT / name)}
for name, args in [('starting-stashes.txt', ('stash', 'list', '--format=%gd %H %s')),
                   ('starting-worktrees.txt', ('worktree', 'list', '--porcelain'))]:
    actual, expected = git(*args), (HERE / name).read_text()
    if 'worktrees' in name:
        def others(text):
            return '\n\n'.join(item for item in text.strip().split('\n\n')
                               if not item.startswith('worktree ' + str(ROOT) + '\n'))
        actual, expected = others(actual), others(expected)
    assert actual == expected, name
assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'origin/main').strip() == (HERE / 'starting-main.txt').read_text().strip()
subprocess.run(['git', 'merge-base', '--is-ancestor', start, 'HEAD'], cwd=ROOT, check=True)
tracked = set(git('ls-files').splitlines())
hs = {name for name in base if name.endswith('.hs')}
active = {name for name in base if name.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}}
assert hs == {name for name in tracked if name.endswith('.hs')}
assert active == {name for name in tracked if name.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}}
assert not set(changed) & (hs | active)
components = json.loads((HERE / 'archived-components.json').read_text())
for component, files in components.items():
    assert {str(p.relative_to(HERE / component)) for p in (HERE / component).rglob('*') if p.is_file()} == set(files)
    for name, expected in files.items():
        assert sha(HERE / component / name) == expected
report = dict(status='PASS', baseline_files=len(base), changed=sorted(changed),
              unchanged_haskell_files=len(hs), unchanged_package_files=len(active),
              unchanged_older_non_audit_sources=sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean')
                  and name != 'lean/MicroCFTA/Audit.lean' and name not in selected for name in base),
              frozen_registry_count=len(frozen), frozen_entries=sum(item['checked'] for item in frozen.values()),
              frozen_manifests=frozen, frozen_entry_archives=archives,
              stashes_preserved=True, other_worktrees_preserved=True,
              haskell_fix_registry_first_and_retained=True, archived_components=len(components))
print(json.dumps(report, indent=2))
