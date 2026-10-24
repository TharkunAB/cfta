import hashlib
import json
import subprocess
from pathlib import Path
area=Path('/tmp/mcfta-derived-scalar-shape-20261024/native-names');area.mkdir()
report=[]
for module,constructor in [('Control','Constructor'),('MagicHashConstructor','Constructor#')]:
    source=area/(module+'.hs')
    source.write_text('{-# LANGUAGE DeriveGeneric, MagicHash, TemplateHaskell #-}\nmodule '+module+' where\nimport Data.CFTA.TH (deriveNode)\ndata Hashy = '+constructor+'\n$(deriveNode \'\'Hashy)\n')
    command=['nix-shell','--run','export PATH=/usr/bin:$PATH; cabal exec -- ghc-9.14.1 -v0 -fno-code -fforce-recomp -hide-all-packages -package-id base-4.22.0.0-fde1 -package-id cfta-th-0.1.0.0-inplace '+str(source)]
    result=subprocess.run(command,cwd='/home/tritlo/Code/mcfta',capture_output=True)
    raw=result.stdout+result.stderr;(area/(module+'.log')).write_bytes(raw)
    report.append(dict(module=module,command=command,exit_code=result.returncode,raw_bytes=len(raw),raw_sha256=hashlib.sha256(raw).hexdigest(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
    print(json.dumps(report[-1]));print(raw.decode())
(area/'report.json').write_text(json.dumps(report,indent=2)+'\n')
assert report[0]['exit_code']==0
