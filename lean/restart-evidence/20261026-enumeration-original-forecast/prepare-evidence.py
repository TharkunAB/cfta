from pathlib import Path
import gzip,hashlib,json,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-enumeration-original-forecast-20261026')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
subprocess.run(['python3',str(area/'verify-checks.py')],check=True)
subprocess.run(['python3',str(area/'contracts.py')],check=True)
base=(area/'base.txt').read_text().strip();main=(area/'main.txt').read_text().strip()
subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=root,check=True)
commits=json.loads((area/'source-commits.json').read_text())
assert git('rev-parse','HEAD').decode().strip()==commits[-1]['commit']
finals=json.loads((area/'final-strict.json').read_text())
for module in finals:
    rel='lean/MicroCFTA/'+module+'.lean';data=(root/rel).read_bytes()
    assert data==(area/'sources'/Path(rel).name).read_bytes()==git('show','HEAD:'+rel)
content=json.loads((area/'handoff-content.json').read_text())
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
for rel in docs:
    text=(root/rel).read_text();assert text.count(content['block'])==1
    stripped=text.replace(content['block'],'',1)
    if rel=='FINDINGS.md':
        assert text.count(content['findings'])==1;stripped=stripped.replace(content['findings'],'',1)
        assert text.index('## Haskell fix handoff')<text.index(content['block'].splitlines()[0])
    assert stripped.encode()==git('show',base+':'+rel),rel
note='lean/notes-current-pruning-enumeration-original-forecast.md'
assert (root/note).read_text()==content['note']
assert set(git('diff','--name-only').decode().splitlines())==set(docs)
assert all(rel==note or rel.startswith('lean/restart-evidence/20261026-enumeration-original-forecast/') for rel in git('ls-files','--others','--exclude-standard').decode().splitlines())
assert not git('diff','--cached','--name-only')
for rel in docs+[note]:
    data=(root/rel).read_bytes();assert data.endswith(b'\n') and all(line.rstrip()==line for line in data.splitlines()),rel
for name in ['review-forecast.txt','review-prefix.txt','review-composition.txt']:
    review=(area/name).read_text();assert 'CLEAR' in review
for module in finals:
    if module=='Audit':continue
    sha=hashlib.sha256((root/'lean/MicroCFTA'/f'{module}.lean').read_bytes()).hexdigest()
    assert any(sha in (area/name).read_text() for name in ['review-forecast.txt','review-prefix.txt','review-composition.txt']),module
files=[p for p in sorted(area.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
assert all(not p.is_symlink() for p in files)
target=root/'lean/restart-evidence/20261026-enumeration-original-forecast'
if target.exists():
    previous=json.loads((target/'manifest.json').read_text())
    assert {p.relative_to(target).as_posix() for p in target.rglob('*') if p.is_file()}==set(previous)|{'manifest.json'}
    for rel,entry in previous.items():
        data=(target/rel).read_bytes();assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256']
    for rel in previous:(target/rel).unlink()
    (target/'manifest.json').unlink()
else:target.mkdir(parents=True)
manifest={}
for p in files:
    rel=p.relative_to(area).as_posix();data=p.read_bytes()
    if rel=='strict-original-1/raw.log':
        original=data;data=gzip.compress(data,mtime=0);rel+='.gz';assert gzip.decompress(data)==original
    dest=target/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
    manifest[rel]={'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
(target/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
result={'evidence':str(target.relative_to(root)),'payload_files':len(manifest),'payload_bytes':sum(v['bytes'] for v in manifest.values()),'manifest_sha256':hashlib.sha256((target/'manifest.json').read_bytes()).hexdigest(),'docs':docs+[note],'source_paths':['lean/MicroCFTA/'+name+'.lean' for name in finals]}
Path('/tmp/mcfta-original-forecast-evidence.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
