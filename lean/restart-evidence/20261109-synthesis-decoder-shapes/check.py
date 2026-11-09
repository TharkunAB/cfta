"""Reproduce the public synthesis decoder regression under the project cap."""
from pathlib import Path
import subprocess, json, hashlib, tempfile, shlex, datetime
root = Path(__file__).resolve().parents[3]
packet = Path(__file__).parent
sources = ['cfta-generator/src/Data/CFTA/Gen/Synthesis.hs', 'cfta-generator/test/Data/CFTA/Gen/SynthesisSpec.hs', 'cfta-generator/cfta-generator.cabal']
hashes = {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in sources}
group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
limits = {name: (cgroup / name).read_text().strip() for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert limits == {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}, limits
regression = json.loads((packet / 'tests.json').read_text())
assert regression['passed']
assert all(hashes[name] == expected for name, expected in regression['source_hashes'].items())
expression = 'let pkgs = import <nixpkgs> {}; in pkgs.mkShell { inputsFrom = [ (import ./shell.nix { inherit pkgs; }) ]; packages = [ pkgs.gmp ]; }'
code = '{-# LANGUAGE OverloadedStrings #-}\nmodule Main (main) where\n\nimport Control.Monad (unless)\nimport qualified Data.CFTA.Equality as E\nimport qualified Data.CFTA.Gen.Equality as G\nimport Data.CFTA.Gen.Synthesis\nimport Data.CFTA.Symbol (Symbol, symbolText)\nimport qualified Data.CFTA.Term as T\n\n-- | Count the component occurrences of a decoded Program.\nleafCount :: Program -> Int\nleafCount (Var _) = 1\nleafCount (App f x) = leafCount f + leafCount x\n\n-- | Check the typed source witness, decoded value and exact generator count.\nmain :: IO ()\nmain = do\n    let typ = TCons "app" [TCons "A" [], TCons "B" []]\n        lib = Library [("filter", typ, ["filter"])] [] [] FirstOrder\n        query = Query [] typ\n        annotation = T.Node "app" [T.Node "A" [], T.Node "B" []] :: T.Term Symbol\n        witness = T.Node "filter" [annotation, T.Node "filter" [annotation]]\n        raw = rawSearchSpace lib query 1\n        generated = programsOfSize lib query 1\n        listed = solutionsOfSize lib query 1\n        predicted = Var "filter"\n    print ("raw accepts witness", E.accepts raw witness)\n    print ("raw terms", map (fmap symbolText) (E.terms raw))\n    print ("solutionsOfSize", listed)\n    print ("programsOfSize cardinality", G.cardinality generated)\n    print ("programsOfSize values", G.values generated)\n    print ("decoded component counts", fmap (map leafCount) (G.values generated))\n    unless (E.accepts raw witness && E.terms raw == [witness]) $\n        fail "The raw source-language prediction differs."\n    unless (listed == [predicted] && G.cardinality generated == Right 1\n            && G.values generated == Right [predicted]) $\n        fail "The decoder does not retain the component name or exact count."\n'
results = []
with tempfile.TemporaryDirectory(prefix='mcfta-decoder-shapes-') as tmp:
    source = Path(tmp) / 'Main.hs'
    source.write_text(code)
    commands = [['cabal','build','-j1','--offline','cfta:lib:cfta','cfta-generator:lib:cfta-generator'], ['cabal','exec','--offline','--','runghc-9.14.1','-package-id=cfta-0.1.0.0-inplace','-package-id=cfta-generator-0.1.0.0-inplace',str(source)]]
    for command in commands:
        run = subprocess.run(['nix-shell','--expr',expression,'--run',shlex.join(command)], cwd=root, capture_output=True, text=True, timeout=300)
        results.append({'phase':'build' if len(results)==0 else 'reproduction','exit':run.returncode,'output':(run.stdout+run.stderr)[-8000:]})
        if run.returncode:
            print(json.dumps({'passed':False,'results':results},indent=2));raise SystemExit(run.returncode)
assert hashes == {name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
print(json.dumps({'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits,'passed':True,'all_snapshots_exact':True,'source_hashes':hashes,'regression_tests_recorded':True,'results':results},indent=2))
