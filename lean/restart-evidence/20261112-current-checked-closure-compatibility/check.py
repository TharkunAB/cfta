from pathlib import Path
from collections import deque
import subprocess,json,hashlib,datetime,os,time,re
r=Path(__file__).parent
root=Path(__file__).resolve().parents[3]
m=json.loads((r/'frontier.json').read_text())
def check_sources():
 for module,expected in m['source_hashes'].items():
  assert hashlib.sha256((root/'lean/MicroCFTA'/ (module+'.lean')).read_bytes()).hexdigest()==expected,module
check_sources()
group=next(line.split(':',2)[2]for line in Path('/proc/self/cgroup').read_text().splitlines()if line.startswith('0::'))
cgroup=Path('/sys/fs/cgroup')/group.lstrip('/')
limits={name:(cgroup/name).read_text().strip()for name in ['memory.max','memory.high','memory.swap.max']}
assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},limits
results=[]
for module in m['frontier']:
 tail=deque(maxlen=180);errors=[];capture=0;lines=0;started=time.monotonic()
 print(json.dumps({'building':module,'at':datetime.datetime.now().astimezone().isoformat()}),flush=True)
 env=dict(os.environ);env.pop('LEAN_SYSROOT',None);env['LEAN_NUM_THREADS']='1'
 p=subprocess.Popen(['nix-shell',str(root/'shell.nix'),'--run','lake build MicroCFTA.'+module],cwd=root/'lean',env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 assert p.stdout is not None
 for line in p.stdout:
  lines+=1;tail.append(line)
  if 'error:' in line: capture=100
  if capture:
   if line.startswith(('✔ [','⚠ [','✖ [')): capture=0
   else: errors.append(line);capture-=1
 code=p.wait();check_sources()
 result={'module':module,'exit':code,'elapsed_seconds':round(time.monotonic()-started,2),'output_lines':lines}
 results.append(result)
 print(json.dumps(result),flush=True)
 if code:
  print(''.join(errors)+'\n'+''.join(tail))
  break
report={'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits,'cgroup':group,'live_modules':m['live_modules'],'affected_count':m['affected_count'],'frontier':m['frontier'],'audit_imports':m['audit_imports'],'all_snapshots_exact':True,'results':results,'passed':len(results)==len(m['frontier'])and all(x['exit']==0 for x in results)}
trace=(root/'lean/.lake/build/lib/lean/MicroCFTA/Audit.trace').read_text()
counts=re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',trace)
assert counts
report['audit_axiom_theorems']=int(counts[-1])
(r/'checked.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
raise SystemExit(not report['passed'])
