from pathlib import Path
import gzip,hashlib,json,shutil
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-rendering-20261027');target=root/'lean/restart-evidence/20261027-recursive-rendering'
sha=lambda d:hashlib.sha256(d).hexdigest()
original=json.loads((target/'manifest.json').read_text())
assert sha((target/'manifest.json').read_bytes())=='c97f3a064d20f377150fb1154ac57df9c03b9fa0ddee67d8e482f94532925629'
for rel,entry in original.items():
 data=(target/rel).read_bytes();assert len(data)==entry['bytes'] and sha(data)==entry['sha256']
(area/'staging-attempt-1/handoff-content.json').write_bytes((target/'handoff-content.json').read_bytes())
archives={}
for rel in ['upstream.patch','upstream-inputs/diff.patch']:
 path=target/rel;data=path.read_bytes();assert data==(area/rel).read_bytes()
 compressed=gzip.compress(data,mtime=0);assert gzip.decompress(compressed)==data
 path.with_name(path.name+'.gz').write_bytes(compressed);path.unlink()
 archives[rel]={'archive':rel+'.gz','decoded_bytes':len(data),'decoded_sha256':sha(data)}
(area/'compressed-artifacts.json').write_text(json.dumps(archives,indent=2,sort_keys=True)+'\n')
note='lean/notes-current-pruning-native-rendering.md'
a='Raw logs are losslessly compressed with decoded lengths and hashes. The\nmanifest covers every payload.'
b='Raw logs are losslessly compressed with decoded lengths and hashes. The\nfirst documentation stage rejected blank context lines in two raw upstream\npatches. Both patches now use lossless gzip archives with decoded identities.\nThe complete failed staging manifest, check log and script remain. The\nmanifest covers every payload.'
p=root/note;s=p.read_text();assert s.count(a)==1;p.write_text(s.replace(a,b))
p=area/'handoff-content.json';content=json.loads(p.read_text());assert content['note'].count(a)==1;content['note']=content['note'].replace(a,b);p.write_text(json.dumps(content,indent=2)+'\n')
for rel in ['handoff-content.json','compressed-artifacts.json','correct-evidence.py']:
 (target/rel).write_bytes((area/rel).read_bytes())
for path in (area/'staging-attempt-1').rglob('*'):
 if path.is_file():
  dest=target/path.relative_to(area);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(path.read_bytes())
for rel,entry in original.items():
 if rel in archives:
  data=gzip.decompress((target/archives[rel]['archive']).read_bytes())
 elif rel=='handoff-content.json':data=(target/'staging-attempt-1/handoff-content.json').read_bytes()
 else:data=(target/rel).read_bytes()
 assert len(data)==entry['bytes'] and sha(data)==entry['sha256'],rel
manifest={}
for path in sorted(target.rglob('*')):
 if path.is_file() and path!=target/'manifest.json':
  data=path.read_bytes();manifest[path.relative_to(target).as_posix()]={'bytes':len(data),'sha256':sha(data)}
(target/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
summary_path=Path('/tmp/mcfta-recursive-rendering-evidence.json');summary=json.loads(summary_path.read_text())
summary.update(payload_files=len(manifest),payload_bytes=sum(v['bytes'] for v in manifest.values()),manifest_sha256=sha((target/'manifest.json').read_bytes()))
summary_path.write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
