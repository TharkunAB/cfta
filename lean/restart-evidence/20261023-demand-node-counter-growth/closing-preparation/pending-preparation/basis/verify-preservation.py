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
assert len(base) == 118574
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
specs = [('SourceRecursiveIntersectionNativeNodeCounterGrowth', 'selected-source-gate.json', 160, ['step_mono', 'execute_mono', 'resume_mono'])]
expected = {}
for module, gate_name, cap, heads in specs:
    name = 'lean/MicroCFTA/' + module + '.lean'
    gate = json.loads((HERE / gate_name).read_text())
    assert gate['status'] == 'ACCEPTED_STRICT_SOURCE'
    assert gate['source_cap'] == cap and gate['public_heads'] == heads
    assert isinstance(gate['source_lines'], int) and 0 < gate['source_lines'] <= cap
    assert sha(HERE / (module + '.lean')) == gate['source_sha256']
    assert selected[name]['strict'] == gate['selected_strict'] and selected[name]['lines'] == gate['source_lines']
    expected[name] = (gate['source_sha256'], gate['source_lines'])
assert set(selected) == set(expected)
for name, (expected_sha, lines) in expected.items():
    assert selected[name]['sha256'] == expected_sha and sha(ROOT / name) == expected_sha
    assert len((ROOT / name).read_bytes().splitlines()) == lines
assert all(name not in base for name in selected)
assert 'lean/notes-current-native-node-counter-growth.md' not in base
assert (ROOT / 'lean/notes-current-native-node-counter-growth.md').is_file()
assert json.loads((HERE / 'frozen-modules.json').read_text()) == {
    Path(name).stem: pin['sha256'] for name, pin in selected.items()}
assert set(changed) == set(documents) | (set(selected) & set(base)) | {'lean/MicroCFTA/Audit.lean'}, changed
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == 'a295f1f72153365c886484cbeea933809acbc3f7'
audit_original = HERE / 'original-sources/Audit.original.lean.txt'
assert sha(audit_original) == '1f3a43b7fb26827dc930bdddc7d6ee2f0c543cc53821c897ad5062d776f3320f'
assert len(audit_original.read_bytes().splitlines()) == 3142
audit = (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes()
additions = [('import MicroCFTA.' + module + '\n').encode() for module, _gate, _cap, _heads in specs]
restored = audit
for addition in additions:
    assert audit.count(addition) == 1 and audit.index(addition) < audit.index(b'/-!')
    restored = restored.replace(addition, b'', 1)
assert restored == audit_original.read_bytes()
for name in documents:
    update = 'findings-update.md' if name == 'FINDINGS.md' else 'current-update.md'
    assert (ROOT / name).read_text().replace((HERE / update).read_text() + '\n', '', 1) == git('show', start + ':' + name), name
marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
marker += (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n\n'
assert (ROOT / 'FINDINGS.md').read_text().startswith(marker)
previous = json.loads((ROOT / 'lean/restart-evidence/20261023-stored-node-counter-growth/preservation-final.json').read_text())
archives = dict(previous['frozen_entry_archives'])
registries = dict(previous['frozen_manifests'])
assert len(registries) == 318 and sum(pin['checked'] for pin in registries.values()) == 1414
assert len(archives) == 5
assert 'lean/restart-evidence/20261023-stored-node-counter-growth/frozen-modules.json' not in registries
registries['lean/restart-evidence/20261023-stored-node-counter-growth/frozen-modules.json'] = {'checked': 1}
frozen = {}
for name in registries:
    entries = json.loads((ROOT / name).read_text())
    assert len(entries) == registries[name]['checked'], name
    if 'manifest_sha256' in registries[name]:
        assert sha(ROOT / name) == registries[name]['manifest_sha256'], name
    for module, expected in entries.items():
        source = module if '/' in module else 'lean/MicroCFTA/' + module + '.lean'
        if sha(ROOT / source) != expected:
            entry = archives[source]
            assert entry['sha256'] == expected and sha(ROOT / entry['snapshot']) == expected
            assert sha(ROOT / source) == entry['current_sha256']
    frozen[name] = {'checked': len(entries), 'manifest_sha256': sha(ROOT / name)}
assert len(frozen) == 319 and sum(pin['checked'] for pin in frozen.values()) == 1415
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
local_main = (HERE / 'starting-local-main.txt').read_text().strip()
assert local_main == 'ed73f5997f1c07e2961d06e6e290d1de38319dad'
assert git('rev-parse', 'main').strip() == local_main
assert git('rev-parse', 'origin/main').strip() == (HERE / 'starting-main.txt').read_text().strip()
subprocess.run(['git', 'merge-base', '--is-ancestor', start, 'HEAD'], cwd=ROOT, check=True)
tracked = set(git('ls-files').splitlines())
hs = {name for name in base if name.endswith('.hs')}
active = {name for name in base if name.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}}
tracked_hs = {name for name in tracked if name.endswith('.hs')}
assert hs <= tracked_hs
local_archives = {str(path.relative_to(ROOT)) for path in HERE.rglob('*.hs') if path.is_file()}
added_hs = (tracked_hs | local_archives) - hs
for name in added_hs:
    assert name.startswith(str(HERE.relative_to(ROOT)) + '/'), name
    data = (ROOT / name).read_bytes()
    matches = [old for old in hs if base[old]['sha256'] == hashlib.sha256(data).hexdigest()]
    assert matches and any((ROOT / old).read_bytes() == data for old in matches), name
assert active == {name for name in tracked if name.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}}
assert len(hs) == 298 and len(active) == 207
assert not set(changed) & (hs | active)
components = json.loads((HERE / 'archived-components.json').read_text())
for component, files in components.items():
    assert {str(p.relative_to(HERE / component)) for p in (HERE / component).rglob('*') if p.is_file()} == set(files)
    for name, expected in files.items():
        assert sha(HERE / component / name) == expected
older_sources = sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean')
    and name != 'lean/MicroCFTA/Audit.lean' and name not in selected for name in base)
assert older_sources == sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean')
    and name != 'lean/MicroCFTA/Audit.lean' for name in base)
assert older_sources == 3652
report = dict(status='PASS', baseline_files=len(base), changed=sorted(changed),
              unchanged_haskell_files=len(hs), added_haskell_archive_files=len(added_hs), unchanged_package_files=len(active),
              unchanged_older_non_audit_sources=older_sources,
              frozen_registry_count=len(frozen), frozen_entries=sum(item['checked'] for item in frozen.values()),
              frozen_manifests=frozen, frozen_entry_archives=archives,
              audit_only_new_import=True, new_native_node_counter_growth_module_absent_baseline=True,
              stashes_preserved=True, other_worktrees_preserved=True,
              haskell_fix_registry_first_and_retained=True, archived_components=len(components))
print(json.dumps(report, indent=2))
