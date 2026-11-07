"""Check this Lake target, its source, and its public theorem axioms in the project Nix shell."""

import hashlib
import json
import os
from pathlib import Path
import shlex
import signal
import sys
import subprocess
import tempfile


root = Path(__file__).resolve().parents[3]
source = root / "lean/MicroCFTA/SourceSynthesisUniverseProbeReconstruction.lean"
names = json.loads(Path(__file__).with_name("theorems.json").read_text())
assert names and all(name.startswith("MicroCFTA.SourceSynthesisUniverseProbeReconstruction.") for name in names)

body = source.read_bytes()
report = body + "".join(f"\n#print axioms {name}\n" for name in names).encode()
env = dict(os.environ)
env.pop("LEAN_SYSROOT", None)
with tempfile.TemporaryDirectory(prefix="mcfta-universe-original-probe-targets-") as directory:
    target = Path(directory) / "OwnAxiomsReport.lean"
    target.write_bytes(report)
    command = shlex.join(
        ["lake", "env", "lean", "-j1", "-DwarningAsError=true", str(target)]
    )
    build = shlex.join(["lake", "build", "MicroCFTA.SourceSynthesisUniverseProbeReconstruction"])
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
if result.returncode != 0:
    sys.stdout.buffer.write(result.stdout)
    sys.stderr.buffer.write(result.stderr)
    raise SystemExit(result.returncode)
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
