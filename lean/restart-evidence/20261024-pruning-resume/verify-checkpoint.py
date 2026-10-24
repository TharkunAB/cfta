"""Verify pruning resume evidence and exact preservation without compiling."""
import argparse
import gzip
import hashlib
import json
import re
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', type=Path, required=True)
root = parser.parse_args().root.resolve()
here = root / 'lean/restart-evidence/20261024-pruning-resume'
baseline = '74104221af2bdc2d0ccf454658170dd9a253545a'
main = '0db62d26b87e8e55b6c2719f6312ece6f93ed31b'
def sha(data): return hashlib.sha256(data).hexdigest()
def git(*args): return subprocess.check_output(['git', *args], cwd=root)
def load(name): return json.loads((here/name).read_text())
manifest = {}
for line in (here/'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    assert name not in manifest and not Path(name).is_absolute() and '..' not in Path(name).parts
    manifest[name] = digest
assert {p.relative_to(here).as_posix() for p in here.rglob('*') if p.is_file()} == set(manifest) | {'SHA256SUMS'}
for name,digest in manifest.items(): assert sha((here/name).read_bytes()) == digest, name

tree = gzip.decompress((here/'work/baseline-tree.txt.gz').read_bytes())
assert tree == git('ls-tree','-r','-z',baseline)
assert sha(tree) == load('work/baseline.json')['tree_sha256']
changes = load('work/document-changes.json')
repairs = load('work/findings-index-repair.json')
audit_change = load('work/audit-addition.json')
upstream = {x['path']:x for x in load('upstream/merge-report.json')['upstream_changes']}
assert len(upstream) == 2
changed = []; count = 0
for raw in tree.split(b'\0'):
    if not raw: continue
    metadata, raw_name = raw.split(b'\t',1)
    mode, kind, blob = metadata.decode().split(); name=raw_name.decode(); path=root/name
    assert kind=='blob' and ('100755' if path.stat().st_mode&0o111 else '100644')==mode, name
    data=path.read_bytes()
    if name in changes:
        changed.append(name); change=changes[name]
        assert sha(data)==change['after_sha256'], name
        text=data.decode()
        if name=='FINDINGS.md':
            for old,new in reversed(repairs):
                assert text.count(new)==1
                text=text.replace(new,old,1)
        assert sha(text.encode())==change['after_insertion_sha256'],name
        index,addition=change['insertion_character'],change['inserted']
        assert text[index:index+len(addition)]==addition,name
        data=(text[:index]+text[index+len(addition):]).encode()
        assert sha(data)==change['before_sha256'],name
    elif name=='lean/MicroCFTA/Audit.lean':
        changed.append(name); addition=audit_change['prefix'].encode()
        assert data.startswith(addition) and sha(data)==audit_change['after_sha256']
        data=data[len(addition):]; assert sha(data)==audit_change['before_sha256']
    elif name in upstream:
        changed.append(name)
        assert data==git('show',main+':'+name) and sha(data)==upstream[name]['after_sha256']
        data=git('show',baseline+':'+name)
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob,name
    count+=1
assert count==127096 and len(changes)==9 and len(changed)==12
assert git('stash','list','--format=%gd %H %s')==(here/'work/baseline-stashes.txt').read_bytes()
worktrees=(here/'work/baseline-worktrees.txt').read_bytes()
assert git('worktree','list','--porcelain')==worktrees.replace(b'HEAD '+baseline.encode(),b'HEAD '+git('rev-parse','HEAD').strip(),1)
for line in (here/'work/baseline-refs.txt').read_text().splitlines():
    value,ref=line.split()
    if ref not in ['refs/heads/formalize','refs/remotes/origin/formalize','refs/remotes/origin/main']:
        assert git('rev-parse',ref).decode().strip()==value,ref
assert git('rev-parse','origin/main').decode().strip()==main
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
assert git('rev-parse','codex/backup-lpo-main-20261024-0248').decode().strip()==baseline

sources={'SourcePruningPartialMatch':'match-check-2','SourcePruningResume':'resume-check-1'}
for name,attempt in sources.items():
    data=(root/'lean/MicroCFTA'/(name+'.lean')).read_bytes()
    assert data==(here/'production-sources'/(name+'.lean')).read_bytes()
    assert data==(here/'work'/attempt/'checked.lean').read_bytes()
    assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|set_option)\b',data),name
    assert (here/'work'/attempt/'raw.log').read_bytes()==b''
for name in ['pruning-resume','upstream-lpo']:
    assert (here/('notes-current-'+name+'.md')).read_bytes()==(root/'lean'/('notes-current-'+name+'.md')).read_bytes()
findings=(root/'FINDINGS.md').read_text()
assert findings.index('## Haskell fix handoff for external work')<findings.index('## Ordered pruning resume')
index=findings[:findings.index('## Ordered pruning resume')]
assert 'OPEN' not in index and 'Both recorded LPO repairs are merged in PR #169' in index
reports=list((here/'work').glob('*/report.json'))
assert len(reports)==6
for path in reports:
    report=json.loads(path.read_text());raw=(path.parent/'raw.log').read_bytes()
    assert sha(raw)==report['raw_sha256'] and len(raw)==report['raw_bytes']
    assert report['exit_code']==(1 if path.parent.name=='match-check-1' else 0)
    if 'source_sha256' in report:
        assert sha((path.parent/'checked.lean').read_bytes())==report['source_sha256']
        assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']
audit=(here/'work/audit-1/raw.log').read_text()
assert 'Checked axiom dependencies of 75792 MicroCFTA theorems.' in audit
assert 'Build completed successfully (3673 jobs).' in audit
assert len(re.findall(r'^warning:',audit,re.M))==1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public=(here/'work/public-1/raw.log').read_text(); decls=load('work/public-declarations.json')
assert re.findall(r'^@?(MicroCFTA\.[\w.]+) :',public,re.M)==decls['declarations']
assert len(decls['declarations'])==11 and len(public.encode())==6211
axioms=re.findall(r"'(MicroCFTA\.[^']+)' (?:depends on axioms: \[(.*?)\]|(does not depend on any axioms))",public,re.S)
assert [name for name,_,_ in axioms]==decls['theorems'] and len(axioms)==8
for _,names,empty in axioms:
    assert empty or {name.strip().split('.{',1)[0] for name in names.split(',')}<={'propext','Quot.sound'}

validation=load('upstream/validation.json');assert len(validation)==3
for i,report in enumerate(validation):
    raw=(here/'upstream'/f'validation-{i}.log').read_bytes()
    assert report['exit_code']==0 and sha(raw)==report['raw_sha256'] and len(raw)==report['raw_bytes']
assert 'Test suite golden: PASS' in (here/'upstream/validation-0.log').read_text()
for attempt,folder,success in [(1,'',False),(2,'probe-check-2',False),(3,'probe-check-3',True)]:
    where=here/'upstream'/folder
    native=json.loads((where/'probes.json').read_text())
    assert len(native)==(4 if success else 1)
    for report in native:
        raw=(where/(report['probe']+'-'+str(report['stage'])+'.log')).read_bytes()
        assert report['exit_code']==(0 if success else 1)
        assert sha(raw)==report['raw_sha256'] and len(raw)==report['raw_bytes']
        assert sha((here/'upstream'/(report['probe']+'.hs')).read_bytes())==report['source_sha256']
assert '[GT,LT,LT]' in (here/'upstream/probe-check-3/ComparatorRepairProbe-1.log').read_text()
context=(here/'upstream/probe-check-3/ContextRepairProbe-1.log').read_text()
assert '[True,False,True]' in context and 'pruning templates: []' in context
assert load('upstream/merge-report.json')['baseline_files']==count
assert load('upstream/merge-report.json')['proof_work_preserved']
limits=list((here/'inputs').glob('*.limits.json'))
assert len(limits)==10
for path in limits:
    assert json.loads(path.read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
for path in (here/'inputs').glob('*.usage.json'):
    usage=json.loads(path.read_text());assert 0<=usage['age_seconds']<=600 and usage['remaining_percent']>1
for name in ['independent-match-review','independent-resume-review','independent-public-review','independent-document-review']:
    assert (here/'inputs'/('mcfta-pruning-resume-20261024-'+name+'.md')).is_file()
print(json.dumps(dict(status='PASS',baseline=baseline,main=main,baseline_files=count,
    unchanged_files=count-len(changed),exact_changed_files=changed,new_modules=len(sources),
    retained_lean_attempts=len(reports),public_signatures=11,axiom_reports=8,
    upstream_repair_probes='PASS',goldens_and_format='PASS',sealed_files=len(manifest),
    new_compiler_jobs=0,goal='ACTIVE_INCOMPLETE'),indent=2))
