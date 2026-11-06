"""Check the support lemmas and their axioms in the project Nix shell."""

import hashlib
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import tempfile


root = Path(__file__).resolve().parents[3]
source = root / "lean/MicroCFTA/UnionFindSupport.lean"
names = [
    "MicroCFTA.UnionFindSupport.supportedBelow_empty",
    "MicroCFTA.UnionFindSupport.supportedBelow_write",
    "MicroCFTA.UnionFindSupport.supportedBelow_put",
    "MicroCFTA.UnionFindSupport.lt_initialBound_of_mem",
    "MicroCFTA.UnionFindSupport.supportedBelow_withInitialValues",
    "MicroCFTA.UnionFindSupport.supportedBelow_put_of_lt",
    "MicroCFTA.UnionFindSupport.parentsBelow_withInitialValues",
    "MicroCFTA.UnionFindSupport.parentsBelow_put_root",
    "MicroCFTA.UnionFindSupport.parentsBelow_put_parent",
    "MicroCFTA.UnionFindSupport.supportedBelow_mono",
    "MicroCFTA.UnionFindSupport.parentsBelow_mono",
    "MicroCFTA.UnionFindSupport.findRoot_preserves_bounds",
    "MicroCFTA.UnionFindSupport.link_preserves_bounds",
    "MicroCFTA.UnionFindSupport.union_preserves_bounds",
    "MicroCFTA.UnionFindSupport.findRoot_grows_bound",
    "MicroCFTA.UnionFindSupport.union_grows_bound",
    "MicroCFTA.UnionFindSupport.length_le_bound_of_nodup",
    "MicroCFTA.UnionFindSupport.reaches_has_parentDepth",
    "MicroCFTA.UnionFindSupport.raw_parent_of_read",
    "MicroCFTA.UnionFindSupport.parentDepth_executes",
    "MicroCFTA.UnionFindSupport.parentDepth_unique",
    "MicroCFTA.UnionFindSupport.parentDepth_keys",
    "MicroCFTA.UnionFindSupport.parentDepth_le_bound",
    "MicroCFTA.UnionFindSupport.findRoot_uniformFuel",
    "MicroCFTA.UnionFindSupport.findRoot_initial_uniformFuel",
    "MicroCFTA.UnionFindSupport.union_uniformFuel",
    "MicroCFTA.UnionFindSupport.union_initial_uniformFuel",
]
body = source.read_bytes()
report = body + "".join(f"\n#print axioms {name}\n" for name in names).encode()
env = dict(os.environ)
env.pop("LEAN_SYSROOT", None)
with tempfile.TemporaryDirectory(prefix="mcfta-uf-support-") as directory:
    target = Path(directory) / "OwnAxiomsReport.lean"
    target.write_bytes(report)
    command = shlex.join(
        ["lake", "env", "lean", "-j1", "-DwarningAsError=true", str(target)]
    )
    build = shlex.join(["lake", "build", "MicroCFTA.UnionFindSupport"])
    process = subprocess.Popen(
        ["nix-shell", str(root / "shell.nix"), "--run", build + " && exec " + command],
        cwd=root / "lean",
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        output, error = process.communicate(timeout=300)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
        raise
    assert process.returncode is not None
    result = subprocess.CompletedProcess(command, process.returncode, output, error)
assert source.read_bytes() == body, "The source changed during the check."
assert result.returncode == 0, (
    f"Lean check failed with exit {result.returncode}; "
    f"stdout SHA-256 {hashlib.sha256(result.stdout).hexdigest()}."
)
text = result.stdout.decode()
axioms: dict[str, list[str]] = {}
for name in names:
    tail = text.split("'" + name + "'", 1)[1]
    if tail.startswith(" does not depend on any axioms"):
        axioms[name] = []
    else:
        assert tail.startswith(" depends on axioms: [")
        axioms[name] = [
            word.strip()
            for word in tail.split("[", 1)[1].split("]", 1)[0].split(",")
            if word.strip()
        ]
    assert set(axioms[name]) <= {"propext", "Classical.choice", "Quot.sound"}
print(
    json.dumps(
        {
            "compiler_exit": result.returncode,
            "source_sha256": hashlib.sha256(body).hexdigest(),
            "axioms": axioms,
        },
        indent=2,
    )
)
