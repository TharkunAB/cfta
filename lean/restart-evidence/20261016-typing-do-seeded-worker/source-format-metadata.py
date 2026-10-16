#!/usr/bin/env python3
"""Check changed Haskell formatting and active package metadata without edits."""
from pathlib import Path
import json
import subprocess

evidence = Path(__file__).resolve().parent
repository = evidence.parents[2]
inputs = json.loads((evidence / "source-validation-inputs.json").read_text())
packages = ["cfta", "cfta-generator", "cfta-ghc", "decision-model"]
checks = [
    (repository, ["fourmolu", "--mode", "check", *inputs["changed_haskell_files"]], "source-fourmolu.log"),
    (repository, ["cabal-gild", "--mode", "check", *[f"{package}/{package}.cabal" for package in packages]], "source-cabal-gild.log"),
    *[(repository / package, ["cabal", "check"], f"source-metadata-{package}.log") for package in packages],
]
results = []
for cwd, command, name in checks:
    with (evidence / name).open("w") as log:
        result = subprocess.run(command, cwd=cwd, stdout=log, stderr=subprocess.STDOUT, check=False)
    results.append({"cwd": str(cwd), "command": command, "log": name, "exit": result.returncode})
    print(name, result.returncode, flush=True)
(evidence / "source-format-metadata.json").write_text(json.dumps({"changed_haskell_files": inputs["changed_haskell_files"], "results": results}, indent=2) + "\n")
raise SystemExit(0 if all(result["exit"] == 0 for result in results) else 1)
