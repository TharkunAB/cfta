import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*arguments):
    return subprocess.check_output(['git', *arguments], cwd=ROOT, text=True)


baseline = json.loads((HERE / 'starting-files.json').read_text())
changed = []
for name, entry in baseline.items():
    assert (ROOT / name).is_file(), name
    if sha(ROOT / name) != entry['sha256']:
        changed.append(name)
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
trace = 'lean/MicroCFTA/SourceCurrentNativeOriginalPublicationTrace.lean'
assert set(changed) == set(documents + [trace, 'lean/MicroCFTA/Audit.lean']), changed
old = (HERE / 'warm-trace/publication-trace-before.lean.txt').read_bytes()
assert hashlib.sha256(old).hexdigest() == baseline[trace]['sha256']
end = b'\nend MicroCFTA.SourceCurrentNativeOriginalPublicationTrace\n'
current = (ROOT / trace).read_bytes()
assert old.endswith(end) and current.startswith(old[:-len(end)]) and current.endswith(end)
start = (HERE / 'starting-head.txt').read_text().strip()
old_audit = git('show', start + ':lean/MicroCFTA/Audit.lean')
anchor = 'import MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge\n'
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_text() == old_audit.replace(
    anchor, anchor + 'import MicroCFTA.SourceCurrentWarmBuildRowOrigins\n', 1)
previous = json.loads((HERE / 'previous-publication.json').read_text())['preservation']
frozen = {}
for name in previous['frozen_manifests']:
    entries = json.loads((ROOT / name).read_text())
    for module, expected in entries.items():
        source = module if '/' in module else 'lean/MicroCFTA/' + module + '.lean'
        if source == trace:
            assert hashlib.sha256(old).hexdigest() == expected, (name, source)
        else:
            assert sha(ROOT / source) == expected, (name, source)
    frozen[name] = {'checked': len(entries), 'manifest_sha256': sha(ROOT / name)}
for name in ['starting-stashes.txt', 'starting-worktrees.txt']:
    arguments = ('stash', 'list', '--format=%gd %H %s') if 'stashes' in name else ('worktree', 'list', '--porcelain')
    actual = git(*arguments)
    expected = (HERE / name).read_text()
    if 'worktrees' in name:
        actual = '\n\n'.join(block for block in actual.strip().split('\n\n')
                             if not block.startswith('worktree ' + str(ROOT) + '\n'))
        expected = '\n\n'.join(block for block in expected.strip().split('\n\n')
                               if not block.startswith('worktree ' + str(ROOT) + '\n'))
    assert actual == expected, name
assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'origin/main').strip() == (HERE / 'starting-main.txt').read_text().strip()
subprocess.run(['git', 'merge-base', '--is-ancestor', start, 'HEAD'], cwd=ROOT, check=True)
tracked = set(git('ls-files').splitlines())
haskell = {name for name in baseline if name.endswith('.hs')}
packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
active = {name for name in baseline if name.split('/')[0] in packages}
assert haskell == {name for name in tracked if name.endswith('.hs')}
assert active == {name for name in tracked if name.split('/')[0] in packages}
assert not set(changed) & (haskell | active)
findings = (ROOT / 'FINDINGS.md').read_text()
assert findings.startswith('# Current formalization findings\n\n## Haskell fix handoff for external work\n')
assert findings.replace((HERE / 'findings-update.md').read_text(), '', 1) == git('show', start + ':FINDINGS.md')
print(json.dumps({'status': 'PASS', 'baseline_files': len(baseline), 'changed': sorted(changed),
    'unchanged_haskell_files': len(haskell), 'unchanged_package_files': len(active),
    'unchanged_older_non_audit_sources': sum(name.startswith('lean/MicroCFTA/')
        and name.endswith('.lean') and name not in [trace, 'lean/MicroCFTA/Audit.lean'] for name in baseline),
    'additive_module': trace, 'prior_module_archived_byte_exact': True,
    'prior_module_declarations_byte_exact': True,
    'frozen_registry_count': len(frozen), 'frozen_entries': sum(v['checked'] for v in frozen.values()),
    'frozen_manifests': frozen, 'frozen_trace_entry_preserved_in_archive': True,
    'trace_live_hash_intentionally_extended': True,
    'stashes_preserved': True, 'other_worktrees_preserved': True,
    'haskell_fix_registry_first_and_retained': True}, indent=2))
