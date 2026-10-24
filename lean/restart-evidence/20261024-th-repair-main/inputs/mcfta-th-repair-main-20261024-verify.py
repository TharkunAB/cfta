"""Verify the content-identical main merge and complete checkpoint preservation."""
import argparse,gzip,hashlib,json,re,subprocess
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
root=parser.parse_args().root.resolve();here=root/'lean/restart-evidence/20261024-th-repair-main'
baseline='ed89dccbf8242231cde1abf87e52f909cb726470';old_main='c4f7319acf84213fccc8ea389487d4176e4f0b62';main='74250bd889685da436cdbfe32ac4b5a0878ffd09';merge='ea9965949bdad994709318cf54162bea1c23cf40'
def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
def load(name):return json.loads((here/name).read_text())
manifest={}
for line in (here/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1);assert re.fullmatch('[0-9a-f]{64}',digest) and name not in manifest
    assert not Path(name).is_absolute() and '..' not in Path(name).parts;manifest[name]=digest
assert {p.relative_to(here).as_posix() for p in here.rglob('*') if p.is_file()}==set(manifest)|{'SHA256SUMS'}
for name,digest in manifest.items():assert sha((here/name).read_bytes())==digest,name
for args in [('diff','--quiet'),('diff','--cached','--quiet')]:subprocess.run(['git',*args],cwd=root,check=True)
for commit in [old_main,main,merge]:subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=root,check=True)
assert git('rev-parse','origin/main').decode().strip()==main
assert git('rev-list','--parents','-n','1',merge).decode().split()==[merge,baseline,main]
assert git('rev-parse',merge+'^{tree}')==git('rev-parse',baseline+'^{tree}')
assert load('work/merge.json')['commit']==merge and load('work/baseline.json')['head']==baseline
pins=load('work/native-source-pins.json');assert len(pins)==5
assert set(git('diff','--name-only',old_main,main).decode().splitlines())==set(pins)
assert (here/'work/main-delta.patch').read_bytes()==git('diff','--binary',old_main,main)
for name,pin in pins.items():
    data=(root/name).read_bytes();assert data==git('show',main+':'+name)==git('show','07229ca7f3208385a52c442965d8f2dcf73f7d99:'+name)
    assert len(data)==pin['bytes'] and sha(data)==pin['sha256']
    assert git('ls-tree',baseline,'--',name)==git('ls-tree',main,'--',name)
tree=gzip.decompress((here/'work/baseline-tree.txt.gz').read_bytes());assert tree==git('ls-tree','-r','-z',baseline)
assert sha(tree)==load('work/baseline.json')['tree_sha256']
changes=load('work/document-changes.json');index_change=load('work/findings-index-change.json');assert len(changes)==9
changed=[];count=0
for raw in tree.split(b'\0'):
    if not raw:continue
    metadata,raw_name=raw.split(b'\t',1);mode,kind,blob=metadata.decode().split();name=raw_name.decode();path=root/name;data=path.read_bytes()
    assert kind=='blob' and ('100755' if path.stat().st_mode&0o111 else '100644')==mode,name
    if name in changes:
        change=changes[name];assert sha(data)==change['after_sha256'];text=data.decode();position,addition=change['insertion_character'],change['inserted']
        assert text[position:position+len(addition)]==addition
        data=(text[:position]+text[position+len(addition):]).encode();assert sha(data)==change['before_sha256'];changed.append(name)
    if name=='FINDINGS.md':
        assert sha(data)==index_change['after_sha256'] and data.startswith(index_change['after'].encode())
        data=index_change['before'].encode()+data[len(index_change['after'].encode()):];assert sha(data)==index_change['before_sha256']
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob,name
    count+=1
assert count==127926 and len(changed)==9
assert git('stash','list','--format=%gd %H %s')==(here/'work/baseline-stashes.txt').read_bytes()
assert git('worktree','list','--porcelain')==(here/'work/baseline-worktrees.txt').read_bytes().replace(b'HEAD '+baseline.encode(),b'HEAD '+git('rev-parse','HEAD').strip(),1)
for line in (here/'work/baseline-refs.txt').read_text().splitlines():
    value,ref=line.split()
    if ref not in ['refs/heads/formalize','refs/remotes/origin/formalize']:assert git('rev-parse',ref).decode().strip()==value,ref
assert git('rev-parse','codex/backup-th-repair-main-20261024-0421').decode().strip()==baseline
assert (root/'lean/notes-current-th-repair-main.md').read_bytes()==(here/'current-note.md').read_bytes()
findings=(root/'FINDINGS.md').read_text();prefix=findings.split('## Generated-name repair merged on main',1)[0]
assert '## Haskell fix handoff for external work' in prefix and prefix.count('| Fixed by ')==6
assert 'All six repairs are in the imported main history.' in prefix and 'External action: no additional patch.' in prefix
old_rows=[x for x in index_change['before'].splitlines() if x.startswith('| ')][2:]
new_rows=[x for x in index_change['after'].splitlines() if x.startswith('| ')][2:]
assert len(old_rows)==len(new_rows)==6 and old_rows[:5]==new_rows[:5]
for name in ['review','seal-script-review','root-review']:
    assert (here/'inputs'/('mcfta-th-repair-main-20261024-'+name+'.md')).is_file()
limits=list((here/'inputs').glob('*.limits.json'));assert len(limits)==1
for path in limits:assert json.loads(path.read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
usage_paths=list((here/'inputs').glob('*.usage.json'));assert len(usage_paths)==1
for path in usage_paths:
    usage=json.loads(path.read_text());assert 0<=usage['age_seconds']<=600 and usage['remaining_percent']>1
prior=load('previous-publication/remote-publication.json');assert prior['status']=='PUSHED_AND_REMOTE_VERIFIED' and prior['remote_head']==baseline
assert load('previous-publication/publication-spec.json')['head']==baseline
print(json.dumps(dict(status='PASS',baseline=baseline,main=main,merge=merge,merge_tree_identical=True,native_files_identical=5,baseline_files=count,unchanged_files=count-len(changed),exact_changed_files=changed,repairs_merged=6,repeated_builds_or_tests=0,sealed_files=len(manifest),goal='ACTIVE_INCOMPLETE'),indent=2))
