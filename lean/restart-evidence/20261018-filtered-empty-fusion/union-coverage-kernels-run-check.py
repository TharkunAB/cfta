import os, sys, json, subprocess, datetime, hashlib
from pathlib import Path
ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
name, kind, *args = sys.argv[1:]
assert not (HERE/(name+'.json')).exists()
if kind == 'source':
 source = Path(args[0])
 frozen = HERE/(name+'.source.lean')
 assert not frozen.exists()
 frozen.write_bytes(source.read_bytes())
 command = ['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean', '-Dlinter.all=true', str(frozen)]
else:
 assert kind == 'lake'
 command = ['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake', '-d', str(ROOT/'lean'), 'build', *args]
env = dict(os.environ, LEAN_PATH=str(ROOT/'lean/.lake/build/lib/lean'), XDG_RUNTIME_DIR='/run/user/1000', DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus', HEAVY_PEAKS=str(HERE/'union-coverage-kernels-peaks.txt'), NATIVE_CAUSAL_LIMITS=str(HERE/(name+'.limits.json')), NATIVE_CAUSAL_COMMAND=json.dumps(command))
wrapped = ['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(HERE/'union-coverage-kernels-capped-worker.py')]
with (HERE/(name+'.log')).open('xb') as log:
 result = subprocess.run(wrapped, env=env, cwd=ROOT/'lean', stdout=log, stderr=subprocess.STDOUT)
report = dict(command=command, wrapper=wrapped, exit_code=result.returncode, observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), log=name+'.log', limits=name+'.limits.json')
if kind == 'source':
 report.update(source=frozen.name, sha256=hashlib.sha256(frozen.read_bytes()).hexdigest())
(HERE/(name+'.json')).write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report))
if result.returncode:
 print((HERE/(name+'.log')).read_text()[-18000:])
raise SystemExit(result.returncode)
