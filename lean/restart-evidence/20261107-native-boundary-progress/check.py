"""Run bounded native observations. A timeout is not a nontermination proof."""

from pathlib import Path
import datetime
import hashlib
import json
import shlex
import subprocess

root = Path(__file__).resolve().parents[3]
packet = Path(__file__).resolve().parent
expression = "let pkgs = import <nixpkgs> {}; in pkgs.mkShell { inputsFrom = [ (import ./shell.nix { inherit pkgs; }) ]; packages = [ pkgs.gmp ]; }"
sources = [
    root / "lean/repro/RepeatedIntersectionGrowth.hs",
    root / "lean/repro/GeneratedBoundaryEnumerationTimeout.hs",
    packet / "drafts/NativeBoundaryCandidateTrace.hs",
]
hashes = {str(source.relative_to(root)): hashlib.sha256(source.read_bytes()).hexdigest() for source in sources}
subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "cfta"], cwd=root, check=True)
source_tree = subprocess.check_output(["git", "rev-parse", "HEAD:cfta"], cwd=root, text=True).strip()
commands = [["cabal", "build", "lib:cfta", "--offline", "-j1"]]
commands += [["cabal", "exec", "--", "runghc", "-package=cfta", str(source)] for source in sources]
results = []
for command in commands:
    run = subprocess.run(
        ["nix-shell", "--expr", expression, "--run", shlex.join(command)],
        cwd=root, capture_output=True, text=True, timeout=300,
    )
    results.append({"command": command, "exit": run.returncode, "stdout": run.stdout, "stderr": run.stderr})
    if run.returncode:
        print(json.dumps({"results": results}, indent=2))
        raise SystemExit(run.returncode)
assert hashes == {str(source.relative_to(root)): hashlib.sha256(source.read_bytes()).hexdigest() for source in sources}
subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "cfta"], cwd=root, check=True)
print(json.dumps({
    "kind": "bounded native observations, not a nontermination proof",
    "time": datetime.datetime.now().astimezone().isoformat(),
    "source_tree": source_tree,
    "source_sha256": hashes,
    "results": results,
}, indent=2))
