import subprocess,json,hashlib
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-lpo-main-20261024')
commands=[['nix-shell','--run','export PATH=/usr/bin:$PATH; cabal test specftacular:golden -j1 --ghc-options=-Werror --test-show-details=direct --test-options="+RTS -N1 -RTS"'],['fourmolu','--mode','check','specftacular/src/Specftacular/Rewriting.hs'],['cabal-gild','--mode','check','specftacular/specftacular.cabal']]
reports=[]
for i,command in enumerate(commands):
 result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 raw=area/f'validation-{i}.log';raw.write_bytes(result.stdout)
 report=dict(command=command,exit_code=result.returncode,raw_bytes=len(result.stdout),raw_sha256=hashlib.sha256(result.stdout).hexdigest())
 reports.append(report)
 (area/'validation.json').write_text(json.dumps(reports,indent=2)+'\n')
 print(json.dumps(report),flush=True)
 print(result.stdout.decode()[-9000:],flush=True)
 if result.returncode:raise SystemExit(result.returncode)
