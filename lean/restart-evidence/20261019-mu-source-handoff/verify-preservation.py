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
assert not set(changed)-allowed,sorted(set(changed)-allowed)
head=(HERE/'starting-head.txt').read_text().strip()
prior=git('show',head+':lean/MicroCFTA/Audit.lean')
names=json.loads((HERE/'new-modules.json').read_text())
imports=''.join('import MicroCFTA.'+name+'\n' for name in names)
expected=prior.replace('import MicroCFTA.SourceCurrentSelectedPrimaryOrigins\n','import MicroCFTA.SourceCurrentSelectedPrimaryOrigins\n'+imports,1)
assert (ROOT/'lean/MicroCFTA/Audit.lean').read_text()==expected
previous=json.loads((ROOT/'lean/restart-evidence/20261018-native-renewal/preservation-final.json').read_text())
manifest_paths=list(previous['frozen_manifests'])+['lean/restart-evidence/20261019-mu-source-handoff/frozen-modules.json']
frozen={}
for name in manifest_paths:
 entries=json.loads((ROOT/name).read_text())
 for module,expected in entries.items():
  module=module if '/' in module else 'lean/MicroCFTA/'+module+'.lean'
  assert sha(ROOT/module)==expected,(name,module)
 frozen[name]={'checked':len(entries),'manifest_sha256':sha(ROOT/name)}
assert git('stash','list','--format=%gd %H %s')==(HERE/'starting-stashes.txt').read_text()
assert others(git('worktree','list','--porcelain'))==others((HERE/'starting-worktrees.txt').read_text())
assert git('branch','--show-current').strip()=='formalize'
packages={'cfta','cfta-generator','cfta-ghc','decision-model'}
package_files={name for name in baseline if name.split('/',1)[0] in packages}
current_packages={name for name in git('ls-files').splitlines() if name.split('/',1)[0] in packages}
assert package_files==current_packages
assert not package_files & set(changed)
assert not any(name.endswith('.hs') for name in changed)
findings=(ROOT/'FINDINGS.md').read_text()
assert findings.startswith('# Current formalization findings\n\n## Haskell fix handoff for external work\n')
assert 'b9219b9e' in findings[:findings.index('- **Negative typed-language bounds.**')]
old=git('show',head+':FINDINGS.md')
prior_body=old.split('## Haskell fix handoff for external work\n\n',1)[1]
assert prior_body in findings
report={'status':'PASS','baseline_files':len(baseline),'baseline_sha256':sha(HERE/'starting-sha256.json'),'missing':missing,'changed':sorted(changed),'older_non_audit_sources':sum(name.startswith('lean/MicroCFTA/') and name.endswith('.lean') and name!='lean/MicroCFTA/Audit.lean' for name in baseline),'all_starting_haskell_files':sum(name.endswith('.hs') for name in baseline),'all_haskell_unchanged':True,'active_package_files':len(package_files),'active_packages_unchanged':True,'audit_only_adds_declared_imports':True,'stashes':len((HERE/'starting-stashes.txt').read_text().splitlines()),'other_worktrees':len(others(git('worktree','list','--porcelain'))),'frozen_manifest_count':len(frozen),'frozen_module_entries':sum(item['checked'] for item in frozen.values()),'frozen_manifests':frozen,'haskell_fix_registry_first_and_retained':True}
assert report['baseline_files']==37072
assert report['older_non_audit_sources']==3430
assert report['frozen_manifest_count']==188 and report['frozen_module_entries']==1188+len(names)
assert len(names)>0
print(json.dumps(report,indent=2))
