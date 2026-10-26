from pathlib import Path
import hashlib,json,os,subprocess,sys
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-template-copies-main-20261026')
kind,name=sys.argv[1:];run=area/name;run.mkdir()
if kind=='haskell':
 command=['nix-shell','--run','export PATH=/usr/bin:$PATH; cabal test cfta:test:unit-tests --test-show-details=direct --test-options="--match=templates --seed=20261026 +RTS -N1 -RTS" -j1']
elif kind=='format':
 command=['nix-shell','--run','fourmolu --mode check cfta/src/Data/CFTA/Template.hs cfta-generator/src/Data/CFTA/Sized.hs && cabal-gild --input cfta/cfta.cabal --mode check && cabal-gild --input cfta-generator/cfta-generator.cabal --mode check']
elif kind=='audit':
 command=['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','-d',str(root/'lean'),'build','MicroCFTA.Audit']
else:raise ValueError(kind)
result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(run/'raw.log').write_bytes(result.stdout)
unified=next(line.split(':',2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
capdir=Path('/sys/fs/cgroup')/unified.lstrip('/')
limits={key:(capdir/key).read_text().strip() for key in ['memory.max','memory.high','memory.swap.max']}
cap=8589934592 if kind=='haskell' else 4294967296
assert limits=={'memory.max':str(cap),'memory.high':str(cap),'memory.swap.max':'0'}
report=dict(command=command,exit_code=result.returncode,bytes=len(result.stdout),sha256=hashlib.sha256(result.stdout).hexdigest(),cgroup_path=unified,cgroup_limits=limits)
(run/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report));print(result.stdout.decode()[-7000:],end='');raise SystemExit(result.returncode)
