from pathlib import Path
import gzip,hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-rendering-20261027')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
summary=json.loads(Path('/tmp/mcfta-recursive-rendering-evidence.json').read_text())
rel=summary['evidence'];target=root/rel;manifest=json.loads((target/'manifest.json').read_text())
assert hashlib.sha256((target/'manifest.json').read_bytes()).hexdigest()==summary['manifest_sha256']
assert {p.relative_to(target).as_posix() for p in target.rglob('*') if p.is_file()}==set(manifest)|{'manifest.json'}
for name,entry in manifest.items():
 data=(target/name).read_bytes();assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],name
for name,entry in json.loads((target/'compressed-logs.json').read_text()).items():
 data=gzip.decompress((target/entry['archive']).read_bytes())
 assert len(data)==entry['decoded_bytes'] and hashlib.sha256(data).hexdigest()==entry['decoded_sha256']
 report=json.loads((target/str(Path(name).parent)/'report.json').read_text())
 assert report['bytes']==len(data) and report['sha256']==hashlib.sha256(data).hexdigest()
for name,entry in json.loads((target/'compressed-artifacts.json').read_text()).items():
 data=gzip.decompress((target/entry['archive']).read_bytes())
 assert len(data)==entry['decoded_bytes'] and hashlib.sha256(data).hexdigest()==entry['decoded_sha256']
 original=json.loads((target/'staging-attempt-1/manifest.json').read_text())[name]
 assert len(data)==original['bytes'] and hashlib.sha256(data).hexdigest()==original['sha256']
content=json.loads((target/'handoff-content.json').read_text());base=(target/'base.txt').read_text().strip()
for path in content['docs']:
 text=(root/path).read_text();assert text.count(content['block'])==1
 text=text.replace(content['block'],'',1)
 if path=='FINDINGS.md':assert text.count(content['findings'])==1;text=text.replace(content['findings'],'',1)
 assert text.encode()==git('show',base+':'+path),path
assert (root/content['note_path']).read_text()==content['note']
subprocess.run(['python3',str(area/'verify-checks.py')],check=True)
commits=json.loads((area/'source-commits.json').read_text());assert git('rev-parse','HEAD').decode().strip()==commits[-1]['commit']
assert not git('diff','--cached','--name-only')
subprocess.run(['git','add','--',*summary['docs']],cwd=root,check=True)
subprocess.run(['git','add','-f','--',rel],cwd=root,check=True)
expected=set(summary['docs'])|{rel+'/'+name for name in manifest}|{rel+'/manifest.json'}
assert set(git('diff','--cached','--name-only').decode().splitlines())==expected
for path in expected:assert git('show',':'+path)==(root/path).read_bytes(),path
subprocess.run(['git','diff','--cached','--check','--','.',':(exclude)'+rel+'/proof-change.patch'],cwd=root,check=True)
subprocess.run(['git','commit','-m','Record native rendering proofs and upstream extraction findings'],cwd=root,check=True)
head=git('rev-parse','HEAD').decode().strip()
for path in expected:assert git('show',head+':'+path)==(root/path).read_bytes(),path
assert not git('status','--porcelain=v1')
print(json.dumps({'head':head,'committed_paths':len(expected),'clean':True,'manifest_sha256':summary['manifest_sha256']},indent=2))
