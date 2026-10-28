from pathlib import Path
import gzip,hashlib,json,subprocess,sys,tempfile
repo=Path('/home/tritlo/Code/mcfta');snapshot=repo/'lean/restart-evidence/20261028-prepared-models';manifest=json.loads((snapshot/'manifest.json').read_text());head=manifest['source_head']
def sha(b):return hashlib.sha256(b).hexdigest()
def payload(name):
 r=next(r for r in manifest['payloads'] if r['path']==name);b=(snapshot/r['stored']).read_bytes();return gzip.decompress(b) if r['gzip'] else b
# Read an independent committed source export with git cat-file's binary batch protocol.
wanted={}
for n in ['prior-lean-sources.json','prior-strong-sources.json','prior-haskell-sources.json']:
 for r in json.loads(payload(n)):wanted[r['path']]=r['sha256']
for m,h in json.loads(payload('source-validation.json'))['source_hashes'].items():wanted['lean/MicroCFTA/'+m+'.lean']=h
mods=json.loads(payload('modules.json'));audit=''.join('import MicroCFTA.'+m+'\n' for m in mods).encode()+payload('prior-sources/Audit.lean');wanted['lean/MicroCFTA/Audit.lean']=sha(audit)
paths=sorted(wanted);query=''.join(head+':'+path+'\n' for path in paths).encode();result=subprocess.run(['git','cat-file','--batch'],input=query,cwd=repo,stdout=subprocess.PIPE,check=True).stdout;offset=0
for path in paths:
 end=result.index(b'\n',offset);header=result[offset:end].split();assert header[1]==b'blob',path;n=int(header[2]);offset=end+1;body=result[offset:offset+n];offset+=n;assert result[offset:offset+1]==b'\n';offset+=1;assert sha(body)==wanted[path],path
assert offset==len(result)
print(json.dumps(dict(status='pass',source_head=head,independent_committed_source_paths=len(paths),source_bytes=len(result))))
