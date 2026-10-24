import hashlib,json,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-derived-scalar-shape-20261024/name-regression-red');area.mkdir()
assert hashlib.sha256((root/'cfta-th/src/Data/CFTA/TH.hs').read_bytes()).hexdigest()=='f1c7b9a41f6f897a6ecf1ba7e17afadef4622d94c26c12a02f1d7f5252ac6105'
source=area/'MagicHashType.hs'
source.write_text('{-# LANGUAGE DeriveGeneric, MagicHash, TemplateHaskell #-}\nmodule MagicHashType where\nimport Data.CFTA.TH (deriveNode)\ndata Hashy# = Constructor\n$(deriveNode \'\'Hashy#)\n')
commands=[['nix-shell','--run','export PATH=/usr/bin:$PATH; cabal exec -- ghc-9.14.1 -v0 -fno-code -fforce-recomp -hide-all-packages -package-id base-4.22.0.0-fde1 -package-id cfta-th-0.1.0.0-inplace '+str(source)],['nix-shell','--run','export PATH=/usr/bin:$PATH; cabal test cfta-th:node-views -j1 --ghc-options=-Werror --test-show-details=direct --test-options="+RTS -N1 -M1G -RTS"']]
reports=[]
for index,command in enumerate(commands):
 result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 raw=result.stdout;(area/(str(index)+'.log')).write_bytes(raw)
 reports.append(dict(command=command,exit_code=result.returncode,raw_bytes=len(raw),raw_sha256=hashlib.sha256(raw).hexdigest()))
 print(json.dumps(reports[-1]));print(raw.decode())
 assert result.returncode!=0
 if index==0:assert b'Illegal type constructor or class name' in raw and b'Hashy#Node' in raw
 else:assert b'4 examples, 1 failure' in raw and b'[True,True,True,True,True,False,False]' in raw
(area/'report.json').write_text(json.dumps(reports,indent=2)+'\n')
(area/'TH.hs').write_bytes((root/'cfta-th/src/Data/CFTA/TH.hs').read_bytes())
(area/'Spec.hs').write_bytes((root/'cfta-th/test/Spec.hs').read_bytes())
