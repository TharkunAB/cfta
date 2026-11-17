from pathlib import Path
import datetime
import hashlib
import json
import shlex
import os
import signal
import subprocess
import tempfile
import time

ROOT=Path('/home/tritlo/Code/mcfta')
WORK=Path(__file__).resolve().parent
PINS=json.loads((WORK/'source-pins.json').read_text())
SHA=lambda data:hashlib.sha256(data).hexdigest()
for n,d in PINS.items():assert SHA((ROOT/n).read_bytes())==d,n
scratch=Path(tempfile.mkdtemp(prefix='mcfta-fix-self-source-'))
(WORK/'scratch.json').write_text(json.dumps({'owned_directory':str(scratch),'all_objects_disposable_after_terminal':True},indent=2)+'\n')
cgroup=Path('/proc/self/cgroup').read_text().strip().split('::')[-1]
cg=Path('/sys/fs/cgroup')/cgroup.lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.max','memory.high','memory.swap.max']}
assert limits=={'memory.max':'8589934592','memory.high':'8589934592','memory.swap.max':'0'},limits
results=[]
commands=[('build',['cabal','build','cfta:lib:cfta','cfta-generator:lib:cfta-generator','--offline','-j1'],600),
 ('compiler-version',['cabal','exec','--','ghc','--numeric-version'],60),
 ('compile',['cabal','exec','--','ghc','-O0','-package=cfta','-package=cfta-generator','-odir',str(scratch),'-hidir',str(scratch),'-o',str(scratch/'probe'),str(ROOT/'lean/restart-evidence/20261117-source-finite-completion-full-stream-check/Probe.hs')],300),
 ('public',[str(scratch/'probe'),'public','256'],120),
 ('typed-reduced',[str(scratch/'probe'),'typed-reduced','256'],120),
 ('typed-raw',[str(scratch/'probe'),'typed-raw','256'],120)]
commands=[item for item in commands if item[0] not in ['build','compiler-version']]
for name,args,cap in commands:
 start=time.monotonic()
 expression='let pkgs = import <nixpkgs> {}; in pkgs.mkShell { inputsFrom = [ (import ./shell.nix { inherit pkgs; }) ]; packages = [ pkgs.gmp ]; }'
 cmd=['nix-shell','--expr',expression,'--run',shlex.join(args)] if name in ['build','compiler-version','compile'] else args
 state={'phase':name,'command':cmd,'external_timeout_seconds':cap,'cgroup':cgroup,'limits':limits,'started_at':datetime.datetime.now().astimezone().isoformat()}
 (WORK/'running.json').write_text(json.dumps(state,indent=2)+'\n')
 timed_out=False
 with (WORK/(name+'.log')).open('w') as log:
  child_env=dict(os.environ)
  if name in ['public','typed-reduced','typed-raw']:
   child_env['LD_LIBRARY_PATH']='/nix/store/6qi8skh85ci2k9gvl27nnh3kiy32qnsz-zlib-1.3.1/lib:/nix/store/k8bqvzzw3xll9sjkai15skrj7ab4f8gg-gmp-with-cxx-6.3.0/lib'
   state['child_only_LD_LIBRARY_PATH']=child_env['LD_LIBRARY_PATH']
  proc=subprocess.Popen(cmd,cwd=ROOT,env=child_env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  try:code=proc.wait(timeout=cap)
  except subprocess.TimeoutExpired:
   os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=124;timed_out=True
 state.update(exit=code,external_timeout=timed_out,elapsed_seconds=time.monotonic()-start)
 results.append(state)
 (WORK/'results.json').write_text(json.dumps({'phases':results,'all_input_pins_unchanged':all(SHA((ROOT/n).read_bytes())==d for n,d in PINS.items()),'joint_finite_completion_proved':False,'haskell_source_changed':False},indent=2)+'\n')
 print(json.dumps({'phase':name,'exit':code,'external_timeout':timed_out,'elapsed_seconds':state['elapsed_seconds']}),flush=True)
 if code!=0 and name in ['build','compiler-version','compile']:raise SystemExit(code if code>0 else 1)
for n,d in PINS.items():assert SHA((ROOT/n).read_bytes())==d,n
(WORK/'terminal.json').write_text(json.dumps({'at':datetime.datetime.now().astimezone().isoformat(),'all_phases_completed':True,'pins_reverified':len(PINS),'phases':results,'no_source_defect_claim_from_driver':True},indent=2)+'\n')
