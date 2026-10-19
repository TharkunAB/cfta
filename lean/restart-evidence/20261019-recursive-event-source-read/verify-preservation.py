import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
def others(data):return [block for block in data.strip().split('\n\n') if not block.startswith(f'worktree {ROOT}\n')]
baseline=json.loads((HERE/'starting-sha256.json').read_text())
missing=[name for name in baseline if not (ROOT/name).is_file()]
changed=[name for name,expected in baseline.items() if (ROOT/name).is_file() and sha(ROOT/name)!=expected]
authorities={'NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md'}
allowed=authorities|{'lean/MicroCFTA/Audit.lean','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md','lean/notes-current-outer-progress.md','lean/notes-current-effective-outer-progress.md','lean/notes-current-selected-renewal.md','lean/notes-current-writer-history.md','lean/notes-current-native-renewal.md'}
assert not missing,missing
upstream=json.loads((HERE/'upstream-refresh.json').read_text())
upstream_paths=set(upstream['upstream_paths'])
allowed |= upstream_paths
assert not set(changed)-allowed,sorted(set(changed)-allowed)
for item in upstream['upstream_files']:
 assert sha(ROOT/item['path'])==item['sha256'],item['path']
assert not subprocess.run(['git','merge-base','--is-ancestor',upstream['main'],'HEAD'],cwd=ROOT).returncode
assert git('rev-parse','origin/main').strip()==upstream['main']
assert len(upstream['added_haskell_files'])==1 and len(upstream['changed_existing_haskell_files'])==6
assert {name for name,expected in baseline.items() if name.endswith('.hs') and sha(ROOT/name)!=expected} == set(upstream['changed_existing_haskell_files'])
head=(HERE/'starting-head.txt').read_text().strip()
prior=git('show',head+':lean/MicroCFTA/Audit.lean')
names=json.loads((HERE/'new-modules.json').read_text())
imports=''.join('import MicroCFTA.'+name+'\n' for name in names)
expected=prior.replace('import MicroCFTA.SourceCurrentRecursiveEventObservation\n','import MicroCFTA.SourceCurrentRecursiveEventObservation\n'+imports,1)
assert (ROOT/'lean/MicroCFTA/Audit.lean').read_text()==expected
previous=json.loads((ROOT/'lean/restart-evidence/20261019-recursive-event-observation/preservation-final.json').read_text())
manifest_paths=list(previous['frozen_manifests'])+['lean/restart-evidence/20261019-recursive-event-source-read/frozen-modules.json']
frozen={}
for name in manifest_paths:
 entries=json.loads((ROOT/name).read_text())
 for module,expected in entries.items():
  module=module if '/' in module else 'lean/MicroCFTA/'+module+'.lean'
  assert sha(ROOT/module)==expected,(name,module)
 frozen[name]={'checked':len(entries),'manifest_sha256':sha(ROOT/name)}
assert git('stash','list','--format=%gd %H %s')==(HERE/'starting-stashes.txt').read_text()
assert git('stash','list','--format=%gd %H %s')==(ROOT/'lean/restart-evidence/20261019-recursive-value-ancestry/starting-stashes.txt').read_text()
assert others(git('worktree','list','--porcelain'))==others((HERE/'starting-worktrees.txt').read_text())
assert git('branch','--show-current').strip()=='formalize'
packages={'cfta','cfta-generator','cfta-ghc','decision-model'}
package_files={name for name in baseline if name.split('/',1)[0] in packages}
current_packages={name for name in git('ls-files').splitlines() if name.split('/',1)[0] in packages}
added_package_files={name for name in upstream['added_files'] if name.split('/',1)[0] in packages}
assert package_files|added_package_files==current_packages
assert not (package_files & set(changed))-upstream_paths
assert {name for name in changed if name.endswith('.hs')} == set(upstream['changed_existing_haskell_files'])
findings=(ROOT/'FINDINGS.md').read_text()
assert findings.startswith('# Current formalization findings\n\n## Haskell fix handoff for external work\n')
assert 'b9219b9e' in findings[:findings.index('- **Negative typed-language bounds.**')]
old=git('show',head+':FINDINGS.md')
prior_body=old.split('## Haskell fix handoff for external work\n\n',1)[1]
assert prior_body in findings
report={'status':'PASS','baseline_files':len(baseline),'baseline_sha256':sha(HERE/'starting-sha256.json'),'missing':missing,'changed':sorted(changed),'older_non_audit_sources':sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean') and name!='lean/MicroCFTA/Audit.lean' for name in baseline),'all_starting_haskell_files':sum(name.endswith('.hs') for name in baseline),'haskell_changes_exactly_match_reviewed_upstream':True,'unchanged_starting_haskell_files':261,'active_package_files':len(package_files),'active_package_files_after_import':len(current_packages),'active_packages_preserved_except_recorded_upstream_changes':True,'upstream_main':upstream['main'],'upstream_merge':upstream['merge_commit'],'upstream_added_files':len(upstream['added_files']),'upstream_added_haskell_files':1,'upstream_changed_haskell_files':6,'all_haskell_files_after_import':sum(name.endswith('.hs') for name in git('ls-files').splitlines()),'audit_only_adds_declared_imports':True,'stashes':len((HERE/'starting-stashes.txt').read_text().splitlines()),'other_worktrees':len(others(git('worktree','list','--porcelain'))),'frozen_manifest_count':len(frozen),'frozen_module_entries':sum(item['checked'] for item in frozen.values()),'frozen_manifests':frozen,'haskell_fix_registry_first_and_retained':True}
assert report['baseline_files']==38559
assert report['older_non_audit_sources']==3453
assert report['frozen_manifest_count']==195 and report['frozen_module_entries']==1211+len(names)
assert len(names)>0
print(json.dumps(report,indent=2))
