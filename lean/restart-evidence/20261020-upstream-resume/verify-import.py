import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def others(raw):
    return [block for block in raw.decode().strip().split('\n\n')
            if not block.startswith(f'worktree {ROOT}\n')]

baseline = json.loads((HERE/'starting-sha256.json').read_text())
start = (HERE/'starting-head.txt').read_text().strip()
main = (HERE/'starting-upstream.txt').read_text().strip()
assert main == '9769fe3e921d63836a0be337f19edd3c601f076e'
assert not subprocess.run(['git','merge-base','--is-ancestor',start,'HEAD'],cwd=ROOT).returncode
assert not subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=ROOT).returncode
incoming = git('diff','--name-only','184bba662',main).decode().splitlines()
assert len(incoming) == 10
current_docs = {'NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md',
    'lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md',
    'lean/notes-current-publication-status.md'}
changed = [name for name,expected in baseline.items() if sha(ROOT/name) != expected]
assert set(changed) == current_docs | (set(incoming)&set(baseline))
for name in incoming:
    actual = (ROOT/name).read_bytes()
    upstream = git('show',main+':'+name)
    if name in {'CONTEXT.md','README.md'}:
        with tempfile.TemporaryDirectory(prefix='mcfta-upstream-merge-') as folder:
            paths = [Path(folder)/part for part in ['local','base','upstream']]
            base = git('merge-base',start,main).decode().strip()
            for path,revision in zip(paths,[start,base,main]):
                path.write_bytes(git('show',revision+':'+name))
            expected = subprocess.check_output(['git','merge-file','-p',*map(str,paths)],cwd=ROOT)
            assert actual == expected,name
    elif name == 'cfta/CHANGELOG.md':
        repair = (b'- Keep recursive constructor probes fresh relative to captured ordinary\n'
            b'  references. Reuse that same probe choice when matching a Mu. This avoids\n'
            b'  a pending interning lookup in a closed nested constructor expression.\n\n')
        anchor = b'Before release, the package was called `microcfta`.\n\n'
        assert actual == upstream.replace(anchor,anchor+repair,1)
    else:
        assert actual == upstream, name
haskell = {name for name in baseline if name.endswith('.hs')}
changed_haskell = haskell & set(changed)
assert changed_haskell == {'cfta/src/Data/CFTA.hs','cfta-generator/src/Data/CFTA/Gen/Typing.hs',
    'cfta-generator/test/Data/CFTA/Gen/TypingSpec.hs'}
assert all((ROOT/name).read_bytes()==git('show',main+':'+name) for name in changed_haskell)
assert haskell == {name for name in git('ls-files').decode().splitlines() if name.endswith('.hs')}
lean = {name for name in baseline if name.startswith('lean/MicroCFTA/') and name.endswith('.lean')}
assert not lean & set(changed)
prior = json.loads((ROOT/'lean/restart-evidence/20261019-head-stored-callbacks/preservation-final.json').read_text())
manifest_count = entries = 0
for name in prior['frozen_manifests']:
    data = json.loads((ROOT/name).read_text())
    for module,expected in data.items():
        path = module if '/' in module else 'lean/MicroCFTA/'+module+'.lean'
        assert sha(ROOT/path) == expected,(name,path)
    manifest_count += 1
    entries += len(data)
assert manifest_count == 201 and entries == 1230
assert git('stash','list','--format=%gd %H %s') == (HERE/'starting-stashes.txt').read_bytes()
assert others(git('worktree','list','--porcelain')) == others((HERE/'starting-worktrees.txt').read_bytes())
old = git('show',start+':FINDINGS.md').decode().split('## Haskell fix handoff for external work\n\n',1)[1]
assert old in (ROOT/'FINDINGS.md').read_text()
assert (ROOT/'FINDINGS.md').read_text().startswith('# Current formalization findings\n\n## Haskell fix handoff for external work\n')
assert git('branch','--show-current').decode().strip() == 'formalize'
assert not git('ls-files','--unmerged')
print(json.dumps({'status':'PASS','baseline_files':len(baseline),'changed':sorted(changed),
    'incoming_paths':len(incoming),'starting_haskell':len(haskell),'changed_haskell_exact_upstream':sorted(changed_haskell),
    'other_haskell_unchanged':len(haskell)-len(changed_haskell),'all_prior_lean_sources_unchanged':len(lean),
    'frozen_manifests':manifest_count,'frozen_module_entries':entries,
    'stashes':len((HERE/'starting-stashes.txt').read_text().splitlines()),
    'other_worktrees':len(others(git('worktree','list','--porcelain'))),
    'all_prior_evidence_and_non_scope_files_unchanged':True,'no_local_haskell_behavior_patch':True,
    'original_fix_registry_retained':True,'merge_preserves_both_histories':True},indent=2))
