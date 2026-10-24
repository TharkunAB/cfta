"""Verify the scalar-shape proof, native repair and complete baseline preservation."""
import argparse,gzip,hashlib,json,re,subprocess
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
root=parser.parse_args().root.resolve();here=root/'lean/restart-evidence/20261024-derived-scalar-shape'
baseline='2c8b42421d0f395141a00fdc172a4660acebd9ba';main='c4f7319acf84213fccc8ea389487d4176e4f0b62'
repair='07229ca7f3208385a52c442965d8f2dcf73f7d99';proof='78f985d26b423108396cf8db36bc559eded73dfd'
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
for commit in [main,repair,proof]:subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=root,check=True)
assert git('rev-parse','origin/main').decode().strip()==main

tree=gzip.decompress((here/'work/baseline-tree.txt.gz').read_bytes());assert tree==git('ls-tree','-r','-z',baseline)
assert sha(tree)==load('work/baseline.json')['tree_sha256']
changes=load('work/document-changes.json');audit_change=load('work/audit-addition.json')
index1=load('work/findings-repair-index-change.json');index2=load('work/findings-index-publication-change.json')
pins=load('work/native-repair-pins.json');native=set(pins)-{'FINDINGS.md'}
assert len(native)==5 and len(changes)==9
changed=[];count=0
for raw in tree.split(b'\0'):
    if not raw:continue
    metadata,raw_name=raw.split(b'\t',1);mode,kind,blob=metadata.decode().split()
    name=raw_name.decode();path=root/name;data=path.read_bytes()
    assert kind=='blob' and ('100755' if path.stat().st_mode&0o111 else '100644')==mode,name
    touched=False
    if name in changes:
        touched=True;change=changes[name];assert sha(data)==change['after_sha256'],name
        text=data.decode();position,addition=change['insertion_character'],change['inserted']
        assert text[position:position+len(addition)]==addition,name
        data=(text[:position]+text[position+len(addition):]).encode();assert sha(data)==change['before_sha256'],name
    if name=='FINDINGS.md':
        for change in [index2,index1]:
            assert data==change['after'].encode() and sha(data)==change['after_sha256']
            data=change['before'].encode();assert sha(data)==change['before_sha256']
    elif name in native:
        touched=True;assert sha(data)==pins[name]['sha256'] and len(data)==pins[name]['bytes'],name
        assert data==git('show',repair+':'+name),name
        assert data==(here/'native-repair-sources'/name).read_bytes(),name
        data=git('show',baseline+':'+name)
    elif name=='lean/MicroCFTA/Audit.lean':
        touched=True;addition=audit_change['prefix'].encode()
        assert sha(data)==audit_change['after_sha256'] and data.startswith(addition)
        data=data[len(addition):];assert sha(data)==audit_change['before_sha256']
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob,name
    if touched:changed.append(name)
    count+=1
assert count==127564 and len(changed)==15
assert (here/'work/native-repair.patch').read_bytes()==git('diff','--binary',baseline,repair,'--',*pins)
assert git('stash','list','--format=%gd %H %s')==(here/'work/baseline-stashes.txt').read_bytes()
worktrees=(here/'work/baseline-worktrees.txt').read_bytes()
assert git('worktree','list','--porcelain')==worktrees.replace(b'HEAD '+baseline.encode(),b'HEAD '+git('rev-parse','HEAD').strip(),1)
for line in (here/'work/baseline-refs.txt').read_text().splitlines():
    value,ref=line.split()
    if ref not in ['refs/heads/formalize','refs/remotes/origin/formalize']:assert git('rev-parse',ref).decode().strip()==value,ref
assert git('rev-parse','codex/backup-derived-scalar-shape-20261024-0334').decode().strip()==baseline

source=(root/'lean/MicroCFTA/SourceGeneratedNodeViewShape.lean').read_bytes()
assert source==(here/'production-source.lean').read_bytes()==(here/'work/shape-check-2/checked.lean').read_bytes()
assert sha(source)=='bcf77307a41f47a11e3c5c7862ba8120f575761924e9eeebd47b8fc01a977ae9'
assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|set_option)\b',source)
assert (here/'work/shape-check-2/raw.log').read_bytes()==b''
failed=(here/'work/shape-check-1/checked.lean').read_text();final=source.decode()
def normalized(text):return ''.join(re.sub(r'/\-.*?\-/','',text,flags=re.S).split())
assert normalized(failed.split('private theorem bind_ok_iff',1)[0])==normalized(final.split('private theorem bind_ok_iff',1)[0])
def statements(text):return [normalized(x) for x in re.findall(r'^theorem .*? :=',text,re.M|re.S)]
assert statements(failed)==statements(final) and len(statements(final))==13
assert sha((here/'pre-repair-proposal/SourceGeneratedNodeViewShape.lean').read_bytes())=='3cc1970d98ae37f584181a3d0278bb95aede7e20955c0747e85d435f5f56dfeb'
assert (here/'current-note.md').read_bytes()==(root/'lean/notes-current-derived-scalar-shape.md').read_bytes()
findings=(root/'FINDINGS.md').read_text()
assert findings.index('## Haskell fix handoff for external work')<findings.index('## Generated scalar shape proof')
assert '| Generated scalar-view names ending in #' in findings.split('## Generated scalar shape proof',1)[0]

reports=list((here/'work').glob('*/report.json'));lean_reports=[p for p in reports if 'raw_sha256' in json.loads(p.read_text())]
assert len(lean_reports)==5
for path in lean_reports:
    report=json.loads(path.read_text());raw=(path.parent/'raw.log').read_bytes()
    assert sha(raw)==report['raw_sha256'] and len(raw)==report['raw_bytes']
    assert report['exit_code']==(1 if path.parent.name=='shape-check-1' else 0)
    if 'source_sha256' in report:
        assert sha((path.parent/'checked.lean').read_bytes())==report['source_sha256']
        assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']
audit=(here/'work/audit-1/raw.log').read_text()
assert 'Checked axiom dependencies of 75963 MicroCFTA theorems.' in audit and 'Build completed successfully (3676 jobs).' in audit
assert len(re.findall(r'^warning:',audit,re.M))==1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public=(here/'work/public-1/raw.log').read_text();decls=load('work/public-declarations.json')
assert re.findall(r'^@?(MicroCFTA\.[\w.]+)(?=\s|\s*:)',public,re.M)==decls['declarations'] and len(decls['declarations'])==27
axioms=re.findall(r"'(MicroCFTA\.[^']+)' depends on axioms: \[(.*?)\]",public,re.S)
assert [name for name,_ in axioms]==decls['theorems'] and len(axioms)==13
for _,names in axioms:assert {name.strip().split('.{',1)[0] for name in names.split(',')}=={'propext','Classical.choice','Quot.sound'}

def raw_reports(folder,json_name,filename):
    reports=load('work/'+folder+'/'+json_name)
    for index,report in enumerate(reports):
        raw=(here/'work'/folder/filename.format(index=index)).read_bytes()
        assert len(raw)==report['raw_bytes'] and sha(raw)==report['raw_sha256']
    return reports
native_reports=load('work/native-names/report.json')
for report in native_reports:
    raw=(here/'work/native-names'/(report['module']+'.log')).read_bytes()
    assert len(raw)==report['raw_bytes'] and sha(raw)==report['raw_sha256']
assert [r['exit_code'] for r in native_reports]==[0,1]
red=raw_reports('name-regression-red','report.json','{index}.log');assert [r['exit_code'] for r in red]==[1,1]
assert '[True,True,True,True,True,False,False]' in (here/'work/name-regression-red/1.log').read_text()
green=raw_reports('haskell-green','validation.json','validation-{index}.log');assert [r['exit_code'] for r in green]==[0,0,1]
assert '4 examples, 0 failures' in (here/'work/haskell-green/validation-0.log').read_text()
assert 'Use newtype instead of data' in (here/'work/haskell-green/validation-2.log').read_text()
rest=raw_reports('haskell-green-rest','validation.json','validation-{index}.log');assert [r['exit_code'] for r in rest]==[0,0,0]
assert '--ignore-suggestions' in rest[0]['command']
probes=raw_reports('haskell-green-rest','probe-reports.json','probe-{index}.log');assert [r['exit_code'] for r in probes]==[0,1,1]
for index in [1,2]:assert probes[index]['expected_diagnostic'] in (here/'work/haskell-green-rest'/('probe-'+str(index)+'.log')).read_text()
limits=list((here/'inputs').glob('*.limits.json'));assert len(limits)==9
for path in limits:assert json.loads(path.read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
for path in (here/'inputs').glob('*.usage.json'):
    usage=json.loads(path.read_text());assert 0<=usage['age_seconds']<=600 and usage['remaining_percent']>1
for name in ['name-repair-review','haskell-repair-review','model-review','proof-repair-review','elaboration-review','public-review','document-review','root-review']:
    assert (here/'inputs'/('mcfta-derived-scalar-shape-20261024-'+name+'.md')).is_file()
prior=load('previous-publication/remote-publication.json');assert prior['status']=='PUSHED_AND_REMOTE_VERIFIED' and prior['remote_head']==baseline
assert load('previous-publication/publication-spec.json')['head']==baseline
print(json.dumps(dict(status='PASS',baseline=baseline,main=main,baseline_files=count,unchanged_files=count-len(changed),exact_changed_files=changed,new_modules=1,lean_attempts=5,public_signatures=27,axiom_reports=13,resource_receipts=9,sealed_files=len(manifest),goal='ACTIVE_INCOMPLETE'),indent=2))
