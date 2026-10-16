"""Check source formatting and package metadata after the upstream merge."""

import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
changed = subprocess.run(
    ["git", "diff", "--name-only", "8f85ddb6..ccebf0f7"],
    cwd=root, check=True, text=True, capture_output=True,
).stdout.splitlines()
sources = [path for path in changed if path.endswith(".hs")]
packages = ["cfta", "cfta-generator", "cfta-ghc", "decision-model"]
commands = [
    (root, ["fourmolu", "--mode", "check", *sources]),
    (root, ["cabal-gild", "--mode", "check", *[
        f"{package}/{package}.cabal" for package in packages
    ]]),
    *[(root / package, ["cabal", "check"]) for package in packages],
]
results = []
for directory, command in commands:
    result = subprocess.run(command, cwd=directory, text=True, capture_output=True)
    print(str(directory), command, "exit", result.returncode, flush=True)
    print(result.stdout, end="", flush=True)
    print(result.stderr, end="", flush=True)
    results.append({"cwd": str(directory), "command": command, "exit": result.returncode})
(evidence / "source-format-metadata.json").write_text(json.dumps({
    "changed_haskell_files": sources, "results": results,
}, indent=2) + "\n")
raise SystemExit(0 if all(result["exit"] == 0 for result in results) else 1)
