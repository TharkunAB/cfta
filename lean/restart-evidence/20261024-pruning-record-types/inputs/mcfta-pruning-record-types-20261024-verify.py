"""Verify the pruning callback checkpoint and preserve the complete baseline."""
import argparse,gzip,hashlib,json,re,subprocess
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
root=parser.parse_args().root.resolve();here=root/'lean/restart-evidence/20261024-pruning-record-types'
baseline='824808fb47ccd3ad7a4da2ff423f05c1dc8fa804';main='c4f7319acf84213fccc8ea389487d4176e4f0b62'
proof='83926524d89062128512a9d43814543dd921f953'
def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
def load(name):return json.loads((here/name).read_text())
manifest={}
for line in (here/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    assert re.fullmatch('[0-9a-f]{64}',digest) and name not in manifest
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    manifest[name]=digest
assert {p.relative_to(here).as_posix() for p in here.rglob('*') if p.is_file()}==set(manifest)|{'SHA256SUMS'}
for name,digest in manifest.items():assert sha((here/name).read_bytes())==digest,name
for commit in [main,proof]:subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=root,check=True)
assert git('rev-parse','origin/main').decode().strip()==main
for args in [('diff','--quiet'),('diff','--cached','--quiet')]:subprocess.run(['git',*args],cwd=root,check=True)
assert git('rev-list','--parents','-n','1',proof).decode().split()==[proof,baseline]
assert set(git('diff-tree','--no-commit-id','--name-only','-r',proof).decode().splitlines())=={
    'lean/MicroCFTA/SourcePruningPositions.lean','lean/MicroCFTA/SourcePruningRecordTypes.lean','lean/MicroCFTA/Audit.lean'}
assert load('work/baseline.json')['head']==baseline and load('work/proof-commit.json')['commit']==proof

tree=gzip.decompress((here/'work/baseline-tree.txt.gz').read_bytes());assert tree==git('ls-tree','-r','-z',baseline)
assert sha(tree)==load('work/baseline.json')['tree_sha256']
changes=load('work/document-changes.json');audit_change=load('work/audit-addition.json')
assert len(changes)==9
changed=[];count=0
for raw in tree.split(b'\0'):
    if not raw:continue
    metadata,raw_name=raw.split(b'\t',1);mode,kind,blob=metadata.decode().split()
    name=raw_name.decode();path=root/name;data=path.read_bytes()
    assert kind=='blob' and ('100755' if path.stat().st_mode&0o111 else '100644')==mode,name
    if name in changes:
        change=changes[name];assert sha(data)==change['after_sha256'],name
        text=data.decode();position,addition=change['insertion_character'],change['inserted']
        assert text[position:position+len(addition)]==addition,name
        data=(text[:position]+text[position+len(addition):]).encode();assert sha(data)==change['before_sha256'],name
        changed.append(name)
    elif name=='lean/MicroCFTA/Audit.lean':
        addition=audit_change['prefix'].encode();assert addition==b'import MicroCFTA.SourcePruningRecordTypes\n'
        assert sha(data)==audit_change['after_sha256'] and data.startswith(addition)
        data=data[len(addition):];assert sha(data)==audit_change['before_sha256'];changed.append(name)
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob,name
    count+=1
assert count==127746 and len(changed)==10
assert git('stash','list','--format=%gd %H %s')==(here/'work/baseline-stashes.txt').read_bytes()
worktrees=(here/'work/baseline-worktrees.txt').read_bytes()
assert git('worktree','list','--porcelain')==worktrees.replace(b'HEAD '+baseline.encode(),b'HEAD '+git('rev-parse','HEAD').strip(),1)
for line in (here/'work/baseline-refs.txt').read_text().splitlines():
    value,ref=line.split()
    if ref not in ['refs/heads/formalize','refs/remotes/origin/formalize']:assert git('rev-parse',ref).decode().strip()==value,ref
assert git('rev-parse','codex/backup-pruning-record-types-20261024-0356').decode().strip()==baseline

installation=load('work/installation.json');assert len(installation)==2
for module,pin in installation.items():
    source=(root/'lean/MicroCFTA'/(module+'.lean')).read_bytes()
    assert source==(here/'production-sources'/(module+'.lean')).read_bytes()
    assert source==(here/'work'/pin['check']/'MicroCFTA'/(module+'.lean')).read_bytes()
    assert sha(source)==pin['sha256'] and len(source)==pin['bytes'] and len(source.splitlines())==pin['lines']==209
    assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|set_option)\b',source)
    assert (here/'work'/pin['check']/'raw.log').read_bytes()==b''
def statements(text):return [''.join(x.split()) for x in re.findall(r'^theorem .*? :=',text,re.M|re.S)]
positions=(here/'production-sources/SourcePruningPositions.lean').read_text()
callback=(here/'production-sources/SourcePruningRecordTypes.lean').read_text()
assert statements(positions)==statements((here/'helper-proposal/SourcePruningPositions.lean').read_text()) and len(statements(positions))==22
assert statements(callback)==statements((here/'work/callback-check-1/MicroCFTA/SourcePruningRecordTypes.lean').read_text()) and len(statements(callback))==10
assert callback.split('/-- A pending candidate',1)[0]==(here/'work/callback-check-1/MicroCFTA/SourcePruningRecordTypes.lean').read_text().split('/-- A pending candidate',1)[0]
assert (root/'lean/notes-current-pruning-record-types.md').read_bytes()==(here/'current-note.md').read_bytes()
findings=(root/'FINDINGS.md').read_text();prefix=findings.split('## Type-position recording and callback observations',1)[0]
assert '## Haskell fix handoff for external work' in prefix and prefix.count('| Fixed by ')==5
assert '| Generated scalar-view names ending in #' in prefix and '07229ca7f3' in prefix

frozen=load('helper-proposal/FROZEN.json');pins=load('helper-proposal/pins.json')
assert len(pins)==frozen['payload_files']==16 and frozen['compiler_executed'] is False
assert sha((here/'helper-proposal/SourcePruningPositions.lean').read_bytes())=='3ca5e05619e3b65f7dcd26acae4d90aec3708d734c0ec4903e907f9a8d16e201'
assert sha((here/'helper-proposal/pins.json').read_bytes())==frozen['pins_sha256']
assert {p.relative_to(here/'helper-proposal').as_posix() for p in (here/'helper-proposal').rglob('*') if p.is_file()}==set(pins)|{'pins.json','FROZEN.json'}
for name,pin in pins.items():
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    data=(here/'helper-proposal'/name).read_bytes();assert len(data)==pin['bytes'] and sha(data)==pin['sha256']
for pin in load('helper-proposal/source-index.json')['inputs']:
    relative=Path(pin['path']).relative_to('/home/tritlo/Code/mcfta');data=(root/relative).read_bytes()
    cut=(here/'helper-proposal'/pin['cut_path']).read_bytes()
    assert len(data)==pin['bytes'] and sha(data)==pin['sha256']
    assert cut==b''.join(data.splitlines(keepends=True)[pin['first_line']-1:pin['last_line']])
    assert len(cut)==pin['cut_bytes'] and sha(cut)==pin['cut_sha256']

reports=list((here/'work').glob('*/report.json'))
expected={f'positions-check-{i}' for i in range(1,7)}|{'callback-check-1','callback-check-2','installed-build-1','audit-1','public-1'}
assert {p.parent.name for p in reports}==expected and len(reports)==11
failed={'positions-check-'+str(i) for i in range(1,6)}|{'callback-check-1'}
for path in reports:
    report=json.loads(path.read_text());raw=(path.parent/'raw.log').read_bytes()
    assert sha(raw)==report['raw_sha256'] and len(raw)==report['raw_bytes']
    assert report['exit_code']==(1 if path.parent.name in failed else 0)
    if 'source_sha256' in report:
        sources=list(path.parent.rglob('*.lean'));assert len(sources)==1 and sha(sources[0].read_bytes())==report['source_sha256']
        assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']
audit=(here/'work/audit-1/raw.log').read_text()
assert 'Checked axiom dependencies of 76071 MicroCFTA theorems.' in audit and 'Build completed successfully (3678 jobs).' in audit
assert len(re.findall(r'^warning:',audit,re.M))==1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public=(here/'work/public-1/raw.log').read_text();decls=load('work/public-declarations.json')
assert re.findall(r'^@?(MicroCFTA\.[\w.]+)(?=\s|\s*:)',public,re.M)==decls['declarations'] and len(decls['declarations'])==40
axioms=re.findall(r"'(MicroCFTA\.[^']+)' depends on axioms: \[(.*?)\]",public,re.S)
assert [name for name,_ in axioms]==decls['theorems'] and len(axioms)==32
for _,names in axioms:assert {name.strip().split('.{',1)[0] for name in names.split(',')}<={'propext','Classical.choice','Quot.sound'}
limits=list((here/'inputs').glob('*.limits.json'));assert len(limits)==11
for path in limits:assert json.loads(path.read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
usage_paths=list((here/'inputs').glob('*.usage.json'));assert len(usage_paths)==11
for path in usage_paths:
    usage=json.loads(path.read_text());assert 0<=usage['age_seconds']<=600 and usage['remaining_percent']>1
for name in ['source-review','model-review','positions-review','final-delta-review','public-review','document-review','seal-script-review','root-review']:
    assert (here/'inputs'/('mcfta-pruning-record-types-20261024-'+name+'.md')).is_file()
prior=load('previous-publication/remote-publication.json');assert prior['status']=='PUSHED_AND_REMOTE_VERIFIED' and prior['remote_head']==baseline
assert load('previous-publication/publication-spec.json')['head']==baseline
print(json.dumps(dict(status='PASS',baseline=baseline,main=main,proof=proof,baseline_files=count,unchanged_files=count-len(changed),exact_changed_files=changed,new_modules=2,lean_attempts=11,public_signatures=40,axiom_reports=32,resource_receipts=11,sealed_files=len(manifest),goal='ACTIVE_INCOMPLETE'),indent=2))
