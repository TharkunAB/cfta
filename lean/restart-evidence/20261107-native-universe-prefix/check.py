"""Observe returned type-prefix graphs from the public synthesis constructor."""

from pathlib import Path
import datetime
import hashlib
import json
import shlex
import subprocess


root = Path(__file__).resolve().parents[3]
source = root / "lean/repro/AllTypesPrefixClosure.hs"
before = hashlib.sha256(source.read_bytes()).hexdigest()
subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "cfta", "cfta-generator"], cwd=root, check=True)
expression = "let pkgs = import <nixpkgs> {}; in pkgs.mkShell { inputsFrom = [ (import ./shell.nix { inherit pkgs; }) ]; packages = [ pkgs.gmp ]; }"
commands = [
    ["cabal", "build", "lib:cfta-generator", "--offline", "-j1"],
    ["cabal", "exec", "--", "runghc", "-package=cfta", "-package=cfta-generator", str(source)],
]
results = []
for command in commands:
    run = subprocess.run(["nix-shell", "--expr", expression, "--run", shlex.join(command)],
                         cwd=root, capture_output=True, text=True, timeout=300)
    results.append({"command": command, "exit": run.returncode, "stdout": run.stdout, "stderr": run.stderr})
    if run.returncode:
        print(json.dumps({"results": results}, indent=2))
        raise SystemExit(run.returncode)
assert before == hashlib.sha256(source.read_bytes()).hexdigest()
output = results[-1]["stdout"]
names = ["int", "list", "pair-function", "unequal-depth", "arrow-catalog",
         "missing-rigid-var-e", "fun-unary", "occurs-check"]
reports = [line for line in output.splitlines() if any(line.startswith(name + ": ") for name in names)]
complete = len(reports) == len(names) and all(": Right " in line for line in reports)
observations = sum(line.count("Observation {") for line in reports)
closed = not any("closed = False" in line for line in reports)
same_universe = not any("muSubsetOfActualU = False" in line for line in reports)
checked = complete and observations == 58 and closed and same_universe
print(json.dumps({
    "time": datetime.datetime.now().astimezone().isoformat(),
    "source_sha256": before,
    "source_trees": {name: subprocess.check_output(["git", "rev-parse", "HEAD:" + name], cwd=root, text=True).strip()
                     for name in ["cfta", "cfta-generator"]},
    "results": results,
    "diagnostic": {"complete_cases": complete, "observations": observations,
                   "closed": closed, "only_original_mu": same_universe, "checked": checked},
    "boundary": "Returned stored graphs only; no general closure or total-work theorem.",
}, indent=2))
if not checked:
    raise SystemExit("The bounded sharing diagnostic did not establish its candidate property.")
