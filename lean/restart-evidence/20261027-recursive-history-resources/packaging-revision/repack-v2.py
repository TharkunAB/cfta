from pathlib import Path
import gzip,hashlib,json,re,shutil,subprocess
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-recursive-history-resources-20261027');p=r/'lean/restart-evidence/20261027-recursive-history-resources';old=Path('/tmp/mcfta-history-resources-archive-v1')
assert not old.exists();assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r).decode().strip()==(a/'source-head.txt').read_text().strip()
docs=json.loads((a/'document-paths.json').read_text());paths=docs+[str(p.relative_to(r))]
expected=set(docs)|{str(f.relative_to(r)) for f in p.rglob('*') if f.is_file()}
staged={x.decode() for x in subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=r).split(b'\0') if x};assert staged==expected
failed=subprocess.run(['git','diff','--cached','--check'],cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);assert failed.returncode==2
subprocess.run(['git','restore','--staged','--',*paths],cwd=r,check=True)
shutil.move(p,old);p.mkdir()
manifest=json.loads((old/'manifest.json').read_text());decoded=json.loads((old/'decoded-files.json').read_text());changes=[]
def sha(data):return hashlib.sha256(data).hexdigest()
for record in manifest['files']:
 name=record['path']
 if name=='decoded-files.json':continue
 source=old/name;data=source.read_bytes();assert len(data)==record['bytes'] and sha(data)==record['sha256']
 target=p/name
 if not name.endswith('.gz') and re.search(rb'(?m)^(?:<<<<<<< |=======\r?$|>>>>>>> )',data):
  target=target.with_name(target.name+'.gz');assert not (old/target.relative_to(p)).exists()
  entry=dict(original_path=name,stored_path=str(target.relative_to(p)),bytes=len(data),sha256=sha(data));decoded.append(entry);changes.append(entry)
  data=gzip.compress(data,mtime=0)
 target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
assert len(changes)==3,changes
rev=p/'packaging-revision';rev.mkdir()
shutil.copyfile(old/'manifest.json',rev/'v1-manifest.json')
shutil.copyfile('/tmp/mcfta-repack-history-resources-v2.py',rev/'repack-v2.py')
(rev/'failed-staging-check.log.gz').write_bytes(gzip.compress(failed.stdout,mtime=0))
shutil.copyfile('/tmp/mcfta-history-committed-verification.log',rev/'premature-committed-check.log')
(rev/'report.json').write_text(json.dumps({'reason':'Store historical conflict snapshots as deterministic gzip so git diff --check does not interpret their preserved markers as current source conflicts.','v1_snapshot_preserved_unchanged':str(old),'v1_manifest_sha256':sha((old/'manifest.json').read_bytes()),'frozen_input_area_unchanged':str(a),'changes':changes,'source_or_document_changes':False},indent=2)+'\n')
(p/'decoded-files.json').write_text(json.dumps(decoded,indent=2)+'\n')
files=[]
for f in sorted(p.rglob('*')):
 if f.is_file():
  d=f.read_bytes();files.append(dict(path=str(f.relative_to(p)),bytes=len(d),sha256=sha(d)))
manifest['files']=files;(p/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'payloads':len(files),'archives':len(decoded),'changed_storage':len(changes),'manifest_sha256':sha((p/'manifest.json').read_bytes())}))
