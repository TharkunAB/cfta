from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-driver-arity-20261027')
name,relative,module=sys.argv[1:];run=area/name;run.mkdir();source=run/'MicroCFTA'/(module+'.lean');source.parent.mkdir();shutil.copyfile(area/relative,source)
overlay=Path('/tmp/mcfta-recursive-driver-arity-overlay-20261027');(overlay/'MicroCFTA').mkdir(parents=True,exist_ok=True)
command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-R',str(run),'-DwarningAsError=true','-Dlinter.all=true','-o',str(overlay/'MicroCFTA'/(module+'.olean')),str(source)]
r=subprocess.run(command,cwd=root/'lean',env=dict(os.environ,LEAN_PATH=str(overlay)+':'+str(root/'lean/.lake/build/lib/lean')),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(run/'raw.log').write_bytes(r.stdout)
cgroup=next(l.split(':',2)[2] for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0::'));cap=Path('/sys/fs/cgroup')/cgroup.lstrip('/');limits={k:(cap/k).read_text().strip() for k in ['memory.max','memory.high','memory.swap.max']};assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
report={'command':command,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'exit_code':r.returncode,'bytes':len(r.stdout),'sha256':hashlib.sha256(r.stdout).hexdigest(),'cgroup_path':cgroup,'cgroup_limits':limits,'status':'strict TEMP overlay check only; not installed in repository'}
(run/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report));print(r.stdout.decode()[:7000]);raise SystemExit(r.returncode)
