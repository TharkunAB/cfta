"""Verify the generated-view integration and all original baseline files."""
import argparse
import gzip
import hashlib
import json
import subprocess
from pathlib import Path

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root',type=Path,required=True)
root=parser.parse_args().root.resolve()
here=root/'lean/restart-evidence/20261024-generated-node-views'
baseline='6bc2c8c6a121adf73f489cfd1a59f267d18a54a7'
main='c4f7319acf84213fccc8ea389487d4176e4f0b62'
merge='a7d667f628ee060501126efaf9d19bfe37ecfb72'
def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
def load(name):return json.loads((here/name).read_text())
manifest={}
for line in (here/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    assert name not in manifest and not Path(name).is_absolute() and '..' not in Path(name).parts
    manifest[name]=digest
assert {p.relative_to(here).as_posix() for p in here.rglob('*') if p.is_file()}==set(manifest)|{'SHA256SUMS'}
for name,digest in manifest.items():assert sha((here/name).read_bytes())==digest,name
assert git('show','-s','--format=%P',merge).decode().split()==[baseline,main]
subprocess.run(['git','merge-base','--is-ancestor',merge,'HEAD'],cwd=root,check=True)
assert git('rev-parse','origin/main').decode().strip()==main

tree=gzip.decompress((here/'work/baseline-tree.txt.gz').read_bytes())
assert tree==git('ls-tree','-r','-z',baseline)
assert sha(tree)==load('work/baseline.json')['tree_sha256']
changes=load('work/document-changes.json')
upstream=load('work/merge-report.json')['changed_paths']
assert len(upstream)==10 and len(changes)==9 and not set(upstream)&set(changes)
old_upstream={'.github/workflows/ci.yml','README.md','cabal.project'}
assert old_upstream<=set(upstream)
changed=[];count=0
for raw in tree.split(b'\0'):
    if not raw:continue
    metadata,raw_name=raw.split(b'\t',1);mode,kind,blob=metadata.decode().split()
    name=raw_name.decode();path=root/name;data=path.read_bytes()
    assert kind=='blob' and ('100755' if path.stat().st_mode&0o111 else '100644')==mode,name
    if name in changes:
        changed.append(name);change=changes[name]
        assert sha(data)==change['after_sha256'],name
        text=data.decode();index,addition=change['insertion_character'],change['inserted']
        assert text[index:index+len(addition)]==addition,name
        data=(text[:index]+text[index+len(addition):]).encode()
        assert sha(data)==change['before_sha256'],name
    elif name in old_upstream:
        changed.append(name)
        assert data==git('show',merge+':'+name),name
        data=git('show',baseline+':'+name)
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob,name
    count+=1
assert count==127411 and len(changed)==12
for name in upstream:
    assert (root/name).read_bytes()==git('show',merge+':'+name),name
    assert (here/'upstream-sources'/name).read_bytes()==git('show',main+':'+name),name
assert (here/'work/upstream.patch').read_bytes()==git('diff','--binary','0db62d26b87e8e55b6c2719f6312ece6f93ed31b',main)
assert git('stash','list','--format=%gd %H %s')==(here/'work/baseline-stashes.txt').read_bytes()
worktrees=(here/'work/baseline-worktrees.txt').read_bytes()
assert git('worktree','list','--porcelain')==worktrees.replace(b'HEAD '+baseline.encode(),b'HEAD '+git('rev-parse','HEAD').strip(),1)
for line in (here/'work/baseline-refs.txt').read_text().splitlines():
    value,ref=line.split()
    if ref not in ['refs/heads/formalize','refs/remotes/origin/formalize']:
        assert git('rev-parse',ref).decode().strip()==value,ref
assert git('rev-parse','codex/backup-generated-views-20261024-0324').decode().strip()==baseline
findings=(root/'FINDINGS.md').read_text()
assert findings.index('## Haskell fix handoff for external work')<findings.index('## Generated scalar node views incorporated')
assert findings.split('\n## Generated scalar node views incorporated',1)[0]==git('show',baseline+':FINDINGS.md').decode().split('\n## Concrete template oracle',1)[0]
assert (here/'current-note.md').read_bytes()==(root/'lean/notes-current-generated-node-views.md').read_bytes()
validation=load('work/validation.json');assert len(validation)==4
for index,report in enumerate(validation):
    raw=(here/'work'/('validation-'+str(index)+'.log')).read_bytes()
    assert report['exit_code']==0 and len(raw)==report['raw_bytes'] and sha(raw)==report['raw_sha256']
command=validation[0]['command']
assert command[0]=='nix-shell' and '-j1' in command[2] and '--ghc-options=-Werror' in command[2]
assert '4 examples, 0 failures' in (here/'work/validation-0.log').read_text()
assert 'ghc-9.14.1' in (here/'work/validation-0.log').read_text()
assert validation[1]['command'][0]=='fourmolu'
assert validation[2]['command'][0]=='cabal-gild'
assert 'cabal check' in validation[3]['command'][2]
assert load('inputs/mcfta-generated-views-20261024-tests-1.json')['exit_code']==0
assert load('inputs/mcfta-generated-views-20261024-tests-1.limits.json')=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
usage=load('inputs/mcfta-generated-views-20261024-tests-1.usage.json')
assert 0<=usage['age_seconds']<=600 and usage['remaining_percent']>1
for name in ['independent-source-review','formal-coverage-review','test-review','document-review','root-review']:
    assert (here/'inputs'/('mcfta-generated-views-20261024-'+name+'.md')).is_file()
prior=load('previous-publication/remote-publication.json')
assert prior['status']=='PUSHED_AND_REMOTE_VERIFIED' and prior['remote_head']==baseline
assert load('previous-publication/publication-spec.json')['head']==baseline
print(json.dumps(dict(status='PASS',baseline=baseline,main=main,merge=merge,
    baseline_files=count,unchanged_files=count-len(changed),exact_changed_files=changed,
    upstream_added_files=7,lean_source_changes=0,fresh_hspec_examples=4,
    fresh_validation_commands=4,sealed_files=len(manifest),goal='ACTIVE_INCOMPLETE'),indent=2))
