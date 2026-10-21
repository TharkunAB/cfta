import hashlib,json,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True)
base=json.loads((H/'starting-files.json').read_text())
changed=[]
for name,item in base.items():
 p=R/name;assert p.is_file(),name
 if sha(p)!=item['sha256']:changed.append(name)
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md']
assert set(changed)==set(docs+['lean/MicroCFTA/Audit.lean']),changed
start=(H/'starting-head.txt').read_text().strip()
audit=(R/'lean/MicroCFTA/Audit.lean').read_text()
for module in ['SourceCurrentClassEndpointCorridors']:
 line='import MicroCFTA.'+module+'\n';assert audit.count(line)==1;audit=audit.replace(line,'',1)
assert audit==git('show',start+':lean/MicroCFTA/Audit.lean')
findings=(R/'FINDINGS.md').read_text();assert findings.startswith('# Current formalization findings\n\n## Haskell fix handoff for external work\n')
index=(H/'haskell-repair-index.md').read_text().rstrip()
assert findings.startswith('# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'+index+'\n\n')
assert findings.replace((H/'findings-update.md').read_text()+'\n','',1)==git('show',start+':FINDINGS.md')
for name in docs:
 if name=='FINDINGS.md':continue
 assert (R/name).read_text().replace((H/'current-update.md').read_text()+'\n','',1)==git('show',start+':'+name),name
previous=json.loads((H/'previous-publication.json').read_text())['preservation']
archives=previous['frozen_entry_archives'];registries=dict(previous['frozen_manifests'])
registries['lean/restart-evidence/20261021-raw-corridor-target-caps/frozen-modules.json']={}
frozen={}
for name in registries:
 entries=json.loads((R/name).read_text())
 for module,expected in entries.items():
  source=module if '/' in module else 'lean/MicroCFTA/'+module+'.lean'
  if sha(R/source)!=expected:
   entry=archives[source];assert entry['sha256']==expected
   assert sha(R/entry['snapshot'])==expected and sha(R/source)==entry['current_sha256']
 frozen[name]={'checked':len(entries),'manifest_sha256':sha(R/name)}
for name,args in [('starting-stashes.txt',('stash','list','--format=%gd %H %s')),('starting-worktrees.txt',('worktree','list','--porcelain'))]:
 actual=git(*args);expected=(H/name).read_text()
 if 'worktrees' in name:
  def others(s):return '\n\n'.join(x for x in s.strip().split('\n\n') if not x.startswith('worktree '+str(R)+'\n'))
  actual,expected=others(actual),others(expected)
 assert actual==expected,name
assert git('branch','--show-current').strip()=='formalize'
assert git('rev-parse','origin/main').strip()==(H/'starting-main.txt').read_text().strip()
subprocess.run(['git','merge-base','--is-ancestor',start,'HEAD'],cwd=R,check=True)
tracked=set(git('ls-files').splitlines());hs={n for n in base if n.endswith('.hs')}
packages={'cfta','cfta-generator','cfta-ghc','decision-model'};active={n for n in base if n.split('/')[0] in packages}
assert hs=={n for n in tracked if n.endswith('.hs')}
assert active=={n for n in tracked if n.split('/')[0] in packages}
assert not set(changed)&(hs|active)
print(json.dumps({'status':'PASS','baseline_files':len(base),'changed':sorted(changed),'unchanged_haskell_files':len(hs),'unchanged_package_files':len(active),'unchanged_older_non_audit_sources':sum(n.startswith('lean/MicroCFTA/') and n.endswith('.lean') and n!='lean/MicroCFTA/Audit.lean' for n in base),'frozen_registry_count':len(frozen),'frozen_entries':sum(v['checked'] for v in frozen.values()),'frozen_manifests':frozen,'frozen_entry_archives':archives,'stashes_preserved':True,'other_worktrees_preserved':True,'haskell_fix_registry_first_and_retained':True},indent=2))
