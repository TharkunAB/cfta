import datetime, hashlib, json, os, subprocess, sys
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=Path(__file__).resolve().parent
name,source_name,expected_sha256=sys.argv[1:]
assert name.startswith("cold-rank-semantic-")
source=here/source_name
source_bytes=source.read_bytes()
assert hashlib.sha256(source_bytes).hexdigest()==expected_sha256
assert len(source_bytes.splitlines())<=250
for suffix in [".json",".usage.json",".source.lean",".log",".limits.json"]:
 assert not (here/(name+suffix)).exists()
usage=json.loads(subprocess.check_output(['python3',str(here/'weekly-usage-helper.py')],text=True))
(here/(name+'.usage.json')).write_text(json.dumps(usage,indent=2)+'\n')
assert 0<=usage['age_seconds']<=600 and usage['remaining_percent']>1,usage
frozen=here/(name+'.source.lean')
assert not frozen.exists()
frozen.write_bytes(source_bytes)
command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true',str(frozen)]
wrapped=['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(here/'cold-rank-semantic-capped-worker.py')]
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',LEAN_PATH=str(root/'lean/.lake/build/lib/lean'),XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(here/'cold-rank-semantic-peaks.txt'),COLD_RANK_SEMANTIC_LIMITS=str(here/(name+'.limits.json')),COLD_RANK_SEMANTIC_COMMAND=json.dumps(command))
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (here/(name+'.log')).open('xb') as log:
 result=subprocess.run(wrapped,cwd=root/'lean',env=env,stdout=log,stderr=subprocess.STDOUT)
report=dict(expected_sha256=expected_sha256,source_lines=len(frozen.read_bytes().splitlines()),command=command,wrapper=wrapped,exit_code=result.returncode,started_at=started,observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source=frozen.name,sha256=hashlib.sha256(frozen.read_bytes()).hexdigest(),log=name+'.log',limits=name+'.limits.json')
(here/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
if result.returncode: print((here/(name+'.log')).read_text()[-22000:])
raise SystemExit(result.returncode)
