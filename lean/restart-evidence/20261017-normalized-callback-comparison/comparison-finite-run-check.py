from pathlib import Path
import datetime, hashlib, json, os, shlex, subprocess, sys
ROOT=Path('/home/tritlo/Code/mcfta')
HERE=Path(__file__).resolve().parent
name, source=sys.argv[1:]
snapshot=HERE/(name+'.source.lean')
assert not snapshot.exists()
snapshot.write_bytes(Path(source).read_bytes())
script=HERE/(name+'.sh')
caps=HERE/(name+'.caps')
lean='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
script.write_text('set -eu\ncontrol=$(cut -d: -f3 /proc/self/cgroup)\nfor key in memory.max memory.high memory.swap.max; do cat "/sys/fs/cgroup${control}/${key}"; done > '+shlex.quote(str(caps))+'\nexec '+shlex.quote(lean)+' -Dlinter.all=true '+shlex.quote(str(snapshot))+'\n')
command=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','bash',str(script)]
env=os.environ.copy()
env.update(LEAN_PATH=str(ROOT/'lean/.lake/build/lib/lean'),HEAVY_PEAKS=str(HERE/'comparison-finite-peaks.txt'),XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus')
with (HERE/(name+'.log')).open('xb') as output:
 result=subprocess.run(command,cwd=ROOT/'lean',env=env,stdout=output,stderr=subprocess.STDOUT)
(HERE/(name+'.json')).write_text(json.dumps(dict(command=command,exit_code=result.returncode,source=snapshot.name,source_sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),log=name+'.log',caps=caps.name,timestamp=datetime.datetime.now().astimezone().isoformat(),LEAN_PATH=env['LEAN_PATH']),indent=2)+'\n')
print(name,'exit',result.returncode,'bytes',(HERE/(name+'.log')).stat().st_size)
print((HERE/(name+'.log')).read_text()[:18000])
sys.exit(result.returncode)
