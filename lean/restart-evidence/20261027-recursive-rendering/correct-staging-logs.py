from pathlib import Path
import gzip,hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-rendering-20261027');rel='lean/restart-evidence/20261027-recursive-rendering';target=root/rel
sha=lambda data:hashlib.sha256(data).hexdigest()
manifest_bytes=(target/'manifest.json').read_bytes();assert sha(manifest_bytes)=='8ab99f03f5bdcfd95c8f573b4edd02ff52805fa4876eaeed7266512bf0c6b505'
manifest=json.loads(manifest_bytes);summary_path=Path('/tmp/mcfta-recursive-rendering-evidence.json');summary=json.loads(summary_path.read_text())
expected=set(summary['docs'])|{rel+'/'+name for name in manifest}|{rel+'/manifest.json'}
assert set(subprocess.check_output(['git','diff','--cached','--name-only'],cwd=root).decode().splitlines())==expected
for name,entry in manifest.items():
 data=subprocess.check_output(['git','show',':'+rel+'/'+name],cwd=root);assert len(data)==entry['bytes'] and sha(data)==entry['sha256']
d=area/'staging-attempt-2';d.mkdir();(d/'manifest.json').write_bytes(manifest_bytes);(d/'stage-script.py').write_bytes(Path('/tmp/mcfta-stage-recursive-rendering.py').read_bytes())
command=['git','diff','--cached','--check','--','.',':(exclude)'+rel+'/proof-change.patch'];r=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);assert r.returncode==2
(d/'whitespace.log').write_bytes(r.stdout)
(d/'result.json').write_text(json.dumps(dict(command=command,exit_code=r.returncode,bytes=len(r.stdout),sha256=sha(r.stdout),original_manifest_sha256=sha(manifest_bytes)),indent=2)+'\n')
artifacts=json.loads((target/'compressed-artifacts.json').read_text())
for name in ['staging-attempt-1/whitespace.log','staging-attempt-2/whitespace.log']:
 data=(area/name).read_bytes();archive=name+'.gz';path=target/archive;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(gzip.compress(data,mtime=0));assert gzip.decompress(path.read_bytes())==data
 artifacts[name]=dict(archive=archive,decoded_bytes=len(data),decoded_sha256=sha(data))
 if name in manifest:artifacts[name]['original_manifest']='staging-attempt-2/manifest.json'
 if (target/name).exists():(target/name).unlink()
for path in d.iterdir():
 if path.name!='whitespace.log':
  destination=target/'staging-attempt-2'/path.name;destination.parent.mkdir(parents=True,exist_ok=True);destination.write_bytes(path.read_bytes())
(target/'correct-staging-logs.py').write_bytes(Path(__file__).read_bytes())
(target/'compressed-artifacts.json').write_text(json.dumps(artifacts,indent=2,sort_keys=True)+'\n')
new={}
for path in sorted(target.rglob('*')):
 if path.is_file() and path!=target/'manifest.json':
  data=path.read_bytes();new[path.relative_to(target).as_posix()]={'bytes':len(data),'sha256':sha(data)}
(target/'manifest.json').write_text(json.dumps(new,indent=2,sort_keys=True)+'\n')
summary.update(payload_files=len(new),payload_bytes=sum(e['bytes'] for e in new.values()),manifest_sha256=sha((target/'manifest.json').read_bytes()));summary_path.write_text(json.dumps(summary,indent=2)+'\n')
subprocess.run(['git','restore','--staged','--',*sorted(expected)],cwd=root,check=True)
p=Path('/tmp/mcfta-stage-recursive-rendering.py');s=p.read_text();a=" original=json.loads((target/'staging-attempt-1/manifest.json').read_text())[name]\n assert len(data)==original['bytes'] and hashlib.sha256(data).hexdigest()==original['sha256']"
b=" if name in ['upstream.patch','upstream-inputs/diff.patch'] or 'original_manifest' in entry:\n  original=json.loads((target/entry.get('original_manifest','staging-attempt-1/manifest.json')).read_text())[name]\n  assert len(data)==original['bytes'] and hashlib.sha256(data).hexdigest()==original['sha256']"
assert s.count(a)==1;p.write_text(s.replace(a,b))
print(json.dumps(summary,indent=2))
