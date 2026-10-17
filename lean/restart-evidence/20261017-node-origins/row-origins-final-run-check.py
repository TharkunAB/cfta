from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys
ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
name, source = sys.argv[1:]
snapshot = HERE / (name + '.source.lean')
assert not snapshot.exists()
snapshot.write_bytes(Path(source).read_bytes())
command = ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '10m', '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean', '-Dlinter.all=true', str(snapshot)]
env = os.environ.copy()
env.update(LEAN_PATH=str(ROOT/'lean/.lake/build/lib/lean'), HEAVY_PEAKS=str(HERE/'row-origins-final-peaks.txt'), XDG_RUNTIME_DIR='/run/user/1000', DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus')
with (HERE/(name+'.log')).open('xb') as output:
 result = subprocess.run(command,cwd=ROOT/'lean',env=env,stdout=output,stderr=subprocess.STDOUT)
(HERE/(name+'.json')).write_text(json.dumps(dict(command=command,exit_code=result.returncode,source=snapshot.name,source_sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),log=name+'.log',timestamp=datetime.datetime.now().astimezone().isoformat(),LEAN_PATH=env['LEAN_PATH'],memory_max='4G',swap_max=0),indent=2)+'\n')
print(name,'exit',result.returncode,'bytes',(HERE/(name+'.log')).stat().st_size)
print((HERE/(name+'.log')).read_text()[:20000])
sys.exit(result.returncode)
