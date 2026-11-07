"""Record bounded public Synthesis observations for a documented pruning rule."""
from pathlib import Path
import subprocess,json,hashlib,shlex,datetime
root=Path(__file__).resolve().parents[3]
source=root/"lean/repro/SynthesisRequiredArgumentAvoid.hs"
before=hashlib.sha256(source.read_bytes()).hexdigest()
subprocess.run(["git","diff","--quiet","HEAD","--","cfta","cfta-generator"],cwd=root,check=True)
expression="let pkgs = import <nixpkgs> {}; in pkgs.mkShell { inputsFrom = [ (import ./shell.nix { inherit pkgs; }) ]; packages = [ pkgs.gmp ]; }"
commands=[["cabal","build","lib:cfta-generator","--offline","-j1"],["cabal","exec","--","runghc","-package=cfta-generator",str(source)]]
results=[]
for command in commands:
 run=subprocess.run(["nix-shell","--expr",expression,"--run",shlex.join(command)],cwd=root,capture_output=True,text=True,timeout=300)
 results.append({"command":command,"exit":run.returncode,"stdout":run.stdout,"stderr":run.stderr})
 if run.returncode:
  print(json.dumps({"results":results},indent=2));raise SystemExit(run.returncode)
assert before==hashlib.sha256(source.read_bytes()).hexdigest()
print(json.dumps({"time":datetime.datetime.now().astimezone().isoformat(),"source_sha256":before,"source_trees":{name:subprocess.check_output(["git","rev-parse","HEAD:"+name],cwd=root,text=True).strip() for name in ["cfta","cfta-generator"]},"results":results},indent=2))
