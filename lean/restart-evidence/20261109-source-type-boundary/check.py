from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess


packet = Path(__file__).resolve().parent
root = packet.parents[2]
sources = [
    "cfta-generator/src/Data/CFTA/Gen/Synthesis.hs",
    "cfta-generator/src/Data/CFTA/Gen/Equality.hs",
    "cfta/src/Data/CFTA/Enumeration.hs",
    "cfta/src/Data/CFTA/Equality/Operations.hs",
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


hashes = {name: digest(root / name) for name in sources}
snapshots = {name: digest(packet / name) for name in ["repro.hs", "observed.txt", "audit.md"]}
record = packet / "checked.json"
if record.exists():
    previous = json.loads(record.read_text())
    assert hashes == previous["source_hashes"]
    assert snapshots == previous["packet_hashes"]

limits = {}
cgroup = None
for line in Path("/proc/self/cgroup").read_text().splitlines():
    if line.startswith("0::"):
        cgroup = line[3:]
        break
assert cgroup is not None
for name in ["memory.max", "memory.high", "memory.swap.max"]:
    limits[name] = (Path("/sys/fs/cgroup") / cgroup.lstrip("/") / name).read_text().strip()
assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}

expression = "let pkgs = import <nixpkgs> {}; in pkgs.mkShell { inputsFrom = [ (import ./shell.nix { inherit pkgs; }) ]; packages = [ pkgs.gmp ]; }"
environment = dict(os.environ)
for command in [
    "cabal build cfta-generator:lib:cfta-generator --offline --disable-optimization -j1",
    "fourmolu --mode check " + str(packet / "repro.hs"),
    "cabal-gild --mode check cfta-generator/cfta-generator.cabal",
    "cabal exec -- runghc-9.14.1 -package-id=cfta-generator-0.1.0.0-inplace " + str(packet / "repro.hs"),
]:
    run = subprocess.run(["nix-shell", "-E", expression, "--run", command], cwd=root, env=environment, capture_output=True, text=True)
    if run.returncode:
        raise RuntimeError(run.stdout + run.stderr)
assert run.stdout == (packet / "observed.txt").read_text(), run.stdout + run.stderr
assert hashes == {name: digest(root / name) for name in sources}
assert snapshots == {name: digest(packet / name) for name in snapshots}
report = {
    "at": datetime.datetime.now().astimezone().isoformat(),
    "source_hashes": hashes,
    "packet_hashes": snapshots,
    "limits": limits,
    "library_build_exit": 0,
    "replay_exit": 0,
    "full_output_exact": True,
    "public_concrete_output_defect_established": False,
    "raw_type_truncation_reached": True,
    "reduced_fixture_annotation_exposed": True,
    "encodings": 3,
    "formal_shared_reachability_established": False,
    "passed": True,
}
print(json.dumps(report, indent=2))
