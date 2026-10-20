import argparse,hashlib,json,os,subprocess
from pathlib import Path
HERE=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261020-native-original-union-descent')
ROOT=HERE.parents[2]
parser=argparse.ArgumentParser();parser.add_argument('--remote-file',type=Path);args=parser.parse_args()
def git(*parts):return subprocess.check_output(['git',*parts],cwd=ROOT)
assert git('status','--porcelain')==b'','Worktree must be committed and clean'
head=git('rev-parse','HEAD').decode().strip()
records=git('ls-tree','-r','--full-tree','-z','HEAD').split(b'\0')
tracked=[]
for record in records:
 if not record:continue
 meta,raw=record.split(b'\t',1);mode,kind,oid=meta.decode().split();path=ROOT/os.fsdecode(raw)
 assert kind=='blob',(kind,str(path))
 data=os.fsencode(os.readlink(path)) if mode=='120000' else path.read_bytes()
 actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert actual==oid,str(path)
 if mode in ['100644','100755']:assert bool(path.stat().st_mode&0o111)==(mode=='100755'),str(path)
 tracked.append(os.fsdecode(raw))
index=git('ls-files','--stage','-z').split(b'\0')
head_entries={}
for record in records:
 if record:
  meta,path=record.split(b'\t',1);mode,_,oid=meta.split();head_entries[path]=(mode,oid)
index_entries={}
for record in index:
 if record:
  meta,path=record.split(b'\t',1);mode,oid,stage=meta.split();assert stage==b'0';index_entries[path]=(mode,oid)
assert head_entries==index_entries
checks=[]
for line in (HERE/'SHA256SUMS').read_text().splitlines():
 expected,name=line.split('  ',1);path=ROOT/name
 assert hashlib.sha256(path.read_bytes()).hexdigest()==expected,name
 checks.append(name)
assert set(checks)=={str(path.relative_to(ROOT)) for path in HERE.rglob('*') if path.is_file() and path.name!='SHA256SUMS'}
assert set(checks+[str((HERE/'SHA256SUMS').relative_to(ROOT))])<=set(tracked)
for entry in json.loads((HERE/'root-scope-manifest.json').read_text())['entries']:
 assert hashlib.sha256((ROOT/entry['path']).read_bytes()).hexdigest()==entry['sha256'],entry['path']
result=json.loads(subprocess.check_output(['python3',str(HERE/'verify-checkpoint.py')],cwd=ROOT))
assert result==json.loads((HERE/'checkpoint-validation.json').read_text())
preserved=json.loads(subprocess.check_output(['python3','/tmp/mcfta-native-union-preservation-after-main.py'],cwd=ROOT))
assert preserved==json.loads((HERE/'preservation-final.json').read_text())
report={'head':head,'tracked_blobs_and_modes':len(tracked),'filesystem_index_head_equal':True,'evidence_checksums':len(checks),'checkpoint_matches_retained_report':True,'preservation_passes':True,'clean':True}
if args.remote_file:
 remote=dict(line.split()[::-1] for line in args.remote_file.read_text().splitlines())
 assert remote['refs/heads/formalize']==head
 assert remote['refs/heads/main']=='794903b3fbad3becb8b28736fc33463760731fc7'
 report['remote']=remote
report['source_baseline_main']='9769fe3e921d63836a0be337f19edd3c601f076e'
report['upstream_main_advanced_externally']=True
report['upstream_refresh_pending']=True
print(json.dumps(report,indent=2))
