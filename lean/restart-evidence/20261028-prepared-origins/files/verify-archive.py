from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
p=argparse.ArgumentParser();p.add_argument('snapshot',type=Path);p.add_argument('--live',action='store_true');p.add_argument('--committed',action='store_true');p.add_argument('--reconstruct',type=Path);a=p.parse_args()
snapshot=a.snapshot.resolve();root=snapshot.parents[2];manifest=json.loads((snapshot/'manifest.json').read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def payload(name):
 rec=next(r for r in manifest['payloads'] if r['path']==name);data=(snapshot/rec['stored']).read_bytes();assert len(data)==rec['stored_size'] and sha(data)==rec['stored_sha256'];raw=gzip.decompress(data) if rec['gzip'] else data;assert len(raw)==rec['size'] and sha(raw)==rec['sha256'];return raw
expected={'manifest.json','README.md'}|{r['stored'] for r in manifest['payloads']}
assert {x.relative_to(snapshot).as_posix() for x in snapshot.rglob('*') if x.is_file()}==expected
for r in manifest['payloads']:
 raw=payload(r['path'])
 if a.reconstruct:
  target=a.reconstruct/r['path'];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
 if a.committed:
  rel=(snapshot/r['stored']).relative_to(root).as_posix();assert subprocess.check_output(['git','show','HEAD:'+rel],cwd=root)==(snapshot/r['stored']).read_bytes()
if a.reconstruct:
 assert {x.relative_to(a.reconstruct).as_posix() for x in a.reconstruct.rglob('*') if x.is_file()}=={r['path'] for r in manifest['payloads']}
 for r in manifest['payloads']:assert sha((a.reconstruct/r['path']).read_bytes())==r['sha256']
# Validate each test log's own reported byte identity and resource limits.
reports=[r['path'] for r in manifest['payloads'] if r['path'].count('/')==1 and r['path'].endswith('/report.json')]
for name in reports:
 report=json.loads(payload(name));raw=payload(name.replace('report.json','raw.log'))
 assert len(raw)==report['bytes'] and sha(raw)==report['sha256']
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 # Main tested source snapshots exist for strict/public commands.
 if 'source_sha256' in report:
  folder=name.rsplit('/',1)[0];sources=[r['path'] for r in manifest['payloads'] if r['path'].startswith(folder+'/') and (r['path'].endswith('/public.lean') or r['path'].startswith(folder+'/MicroCFTA/'))]
  assert len(sources)==1 and sha(payload(sources[0]))==report['source_sha256']
public=json.loads(payload('public-validation.json'));full=payload('public-readback-final/raw.log');old=payload('prior-public-readback/raw.log');assert full.startswith(old) and len(full)==public['bytes'] and sha(full)==public['sha256'];assert payload('new-public-blocks.txt')==full[len(old):]
for name,rec in json.loads(payload('document-inverse.json')).items():
 old=payload('prior-documents/'+name);assert sha(old)==rec['before_sha256']
 insertion=payload('document-insertions/findings.md' if name=='FINDINGS.md' else 'document-insertions/common.md')
 first,rest=old.split(b'\n',1);current=first+b'\n'+insertion+rest
 assert sha(current)==rec['after_sha256'] and current.replace(insertion,b'',1)==old
 if a.live:assert (root/name).read_bytes()==current
if a.live:
 for name in ['prior-lean-sources.json','prior-strong-sources.json','prior-haskell-sources.json']:
  for rec in json.loads(payload(name)):assert sha((root/rec['path']).read_bytes())==rec['sha256'],rec['path']
 assert (root/'lean/notes-current-prepared-origins.md').read_bytes()==payload('root-review/notes-current-prepared-origins.md')
 source=json.loads(payload('source-validation.json'))
 for module,digest in source['source_hashes'].items():assert sha((root/'lean/MicroCFTA'/(module+'.lean')).read_bytes())==digest
 imports=''.join('import MicroCFTA.'+m+'\n' for m in json.loads(payload('modules.json'))).encode()
 assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==imports+payload('prior-Audit.lean')
if a.committed:
 for name in ['manifest.json','README.md']:
  assert subprocess.check_output(['git','show','HEAD:'+(snapshot/name).relative_to(root).as_posix()],cwd=root)==(snapshot/name).read_bytes()
# Optional exact comparison against the original frozen TEMP area.
original=Path(manifest['frozen_area'])
if original.exists():
 assert {x.relative_to(original).as_posix() for x in original.rglob('*') if x.is_file()}=={r['path'] for r in manifest['payloads']}
 for r in manifest['payloads']:assert sha((original/r['path']).read_bytes())==r['sha256']
print(json.dumps(dict(status='pass',payloads=len(manifest['payloads']),commands=len(reports),live=a.live,committed=a.committed,reconstructed=bool(a.reconstruct),exact_original_TEMP=original.exists(),manifest_sha256=sha((snapshot/'manifest.json').read_bytes()))))
