from pathlib import Path
import gzip,hashlib,json,shutil,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-selected-edge-language-20261027')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
subprocess.run(['python3',str(area/'verify-checks.py')],check=True)
base=(area/'base.txt').read_text().strip();commits=json.loads((area/'source-commits.json').read_text())
assert git('rev-parse','HEAD').decode().strip()==commits[-1]['commit']
for module in json.loads((area/'final-strict.json').read_text()):
 rel='lean/MicroCFTA/'+module+'.lean'; data=(root/rel).read_bytes()
 assert data==(area/'sources'/Path(rel).name).read_bytes()==git('show','HEAD:'+rel)
content=json.loads((area/'handoff-content.json').read_text());docs=content['docs'];note=content['note_path']
for rel in docs:
 s=(root/rel).read_text();assert s.count(content['block'])==1
 old=s.replace(content['block'],'',1)
 if rel=='FINDINGS.md':
  assert s.count(content['findings'])==1;old=old.replace(content['findings'],'',1)
  assert s.index('## Haskell fix handoff')<s.index(content['block'].splitlines()[0])
 assert old.encode()==git('show',base+':'+rel),rel
assert (root/note).read_text()==content['note']
assert set(git('diff','--name-only').decode().splitlines())==set(docs)
assert not git('diff','--cached','--name-only')
assert set(git('ls-files','--others','--exclude-standard').decode().splitlines())=={note}
for rel in docs+[note]:
 data=(root/rel).read_bytes();assert data.endswith(b'\n') and all(line.rstrip()==line for line in data.splitlines()),rel
compressed={}
for path in sorted(area.rglob('raw.log')):
 data=path.read_bytes();rel=path.relative_to(area).as_posix()
 compressed[rel]={'archive':rel+'.gz','decoded_bytes':len(data),'decoded_sha256':hashlib.sha256(data).hexdigest()}
(area/'compressed-logs.json').write_text(json.dumps(compressed,indent=2,sort_keys=True)+'\n')
(area/'drafts/STATUS.txt').write_text('Original proposals are retained drafts. They are not the final checked sources.\nUse sources/ and final-strict.json for the final checked proof bytes.\n')
files=[p for p in sorted(area.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
assert all(not p.is_symlink() for p in files)
target=root/'lean/restart-evidence/20261027-selected-edge-language';assert not target.exists();target.mkdir(parents=True)
manifest={}
for path in files:
 rel=path.relative_to(area).as_posix();data=path.read_bytes()
 if rel in compressed:
  original=data;data=gzip.compress(data,mtime=0);rel+='.gz';assert gzip.decompress(data)==original
 dest=target/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 manifest[rel]={'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
(target/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
result={'evidence':str(target.relative_to(root)),'payload_files':len(manifest),'payload_bytes':sum(v['bytes'] for v in manifest.values()),'manifest_sha256':hashlib.sha256((target/'manifest.json').read_bytes()).hexdigest(),'docs':docs+[note]}
Path('/tmp/mcfta-selected-edge-language-evidence.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
