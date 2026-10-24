import subprocess,json,hashlib
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-derived-scalar-shape-20261024/haskell-green-rest');area.mkdir()
commands=[
 ['hlint','--ignore-suggestions','cfta-th/src','cfta-th/test'],
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

probes=[('/tmp/mcfta-derived-scalar-shape-20261024/native-names/Control.hs',None),('/tmp/mcfta-derived-scalar-shape-20261024/native-names/MagicHashConstructor.hs','deriveNode Hashy: names ending in # need a manual node view'),('/tmp/mcfta-derived-scalar-shape-20261024/name-regression-red/MagicHashType.hs','deriveNode Hashy#: names ending in # need a manual node view')]
probe_reports=[]
for index,(source,diagnostic) in enumerate(probes):
 command=['nix-shell','--run','export PATH=/usr/bin:$PATH; cabal exec -- ghc-9.14.1 -v0 -fno-code -fforce-recomp -hide-all-packages -package-id base-4.22.0.0-fde1 -package-id cfta-th-0.1.0.0-inplace '+source]
 result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 raw=result.stdout;(area/('probe-'+str(index)+'.log')).write_bytes(raw)
 probe_reports.append(dict(command=command,exit_code=result.returncode,expected_diagnostic=diagnostic,raw_bytes=len(raw),raw_sha256=hashlib.sha256(raw).hexdigest()))
 assert result.returncode==(0 if diagnostic is None else 1)
 assert diagnostic is None or diagnostic.encode() in raw
 assert b'Illegal data constructor name' not in raw and b'Illegal type constructor' not in raw
 print(json.dumps(probe_reports[-1]),flush=True);print(raw.decode(),flush=True)
(area/'probe-reports.json').write_text(json.dumps(probe_reports,indent=2)+'\n')
