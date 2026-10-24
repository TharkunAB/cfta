import subprocess,shlex,json,hashlib
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-lpo-main-20261024')
reports=[]
for name in ['ComparatorRepairProbe','ContextRepairProbe']:
 source=area/(name+'.hs');executable=area/name;obj=area/(name+'-objects');obj.mkdir()
 compile=['cabal','exec','--','ghc','-threaded','-rtsopts','-Wall','-Werror','-package','specftacular','-outputdir',str(obj),str(source),'-o',str(executable)]
 commands=[['nix-shell','--run','export PATH=/usr/bin:$PATH; '+shlex.join(compile)],[str(executable),'+RTS','-M512M','-RTS']]
 for i,command in enumerate(commands):
  result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
  (area/(name+f'-{i}.log')).write_bytes(result.stdout)
  report=dict(probe=name,stage=i,command=command,exit_code=result.returncode,raw_bytes=len(result.stdout),raw_sha256=hashlib.sha256(result.stdout).hexdigest(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
  reports.append(report);(area/'probes.json').write_text(json.dumps(reports,indent=2)+'\n')
  print(json.dumps(report),flush=True);print(result.stdout.decode(),flush=True)
  if result.returncode:raise SystemExit(result.returncode)
