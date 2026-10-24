import subprocess,json,hashlib
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-generated-views-20261024')
commands=[
 ['nix-shell','--run','export PATH=/usr/bin:$PATH; cabal test cfta-th:node-views -j1 --ghc-options=-Werror --test-show-details=direct --test-options="+RTS -N1 -M1G -RTS"'],
 ['fourmolu','--mode','check','cfta-th/src/Data/CFTA/TH.hs','cfta-th/test/Spec.hs'],
 ['cabal-gild','--mode','check','cfta-th/cfta-th.cabal'],
 ['nix-shell','--run','export PATH=/usr/bin:$PATH; cd cfta-th && cabal check'],
]
reports=[]
for i,command in enumerate(commands):
 result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (area/f'validation-{i}.log').write_bytes(result.stdout)
 report=dict(command=command,exit_code=result.returncode,raw_bytes=len(result.stdout),raw_sha256=hashlib.sha256(result.stdout).hexdigest())
 reports.append(report);(area/'validation.json').write_text(json.dumps(reports,indent=2)+'\n')
 print(json.dumps(report),flush=True);print(result.stdout.decode()[-12000:],flush=True)
 if result.returncode:raise SystemExit(result.returncode)
