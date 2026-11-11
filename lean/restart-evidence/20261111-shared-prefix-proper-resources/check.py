"""Check this Lake target, its source, and its public theorem axioms in the project Nix shell."""

import hashlib
import json
import re
import os
from pathlib import Path
import shlex
import signal
import sys
import subprocess
import tempfile


root = Path(__file__).resolve().parents[3]
source = root / "lean/MicroCFTA/SourcePruningEnumerationSharedPrefixProperResources.lean"
names = json.loads(Path(__file__).with_name("theorems.json").read_text())
# These sources use qualified namespaces at the top level.
assert names

body = source.read_bytes()
def public_names(body):
    namespace = None
    names = []
    for line in body.splitlines():
        scope = re.match(r"^namespace\s+([\w.]+)", line)
        if scope:
            name = scope.group(1).removeprefix("_root_.")
            namespace = name if namespace is None or name.startswith("MicroCFTA.") else namespace + "." + name
        end = re.match(r"^end\s+([\w.]+)\s*$", line)
        if end and namespace:
            name = end.group(1)
            if namespace == name:
                namespace = None
            elif namespace.endswith("." + name):
                namespace = namespace[:-(len(name) + 1)]
        law = re.match(r"^theorem\s+([\w.]+)", line)
        if law:
            assert namespace and namespace.startswith("MicroCFTA.")
            names.append(namespace + "." + law.group(1))
    return names
declared = public_names(body.decode())
assert len(names) == len(declared) and set(names) == set(declared), "Public declarations differ."
report = body + "".join(f"\n#check {name}\n#print axioms {name}\n" for name in names).encode()
env = dict(os.environ)
env.pop("LEAN_SYSROOT", None)
env["LEAN_NUM_THREADS"] = "1"
with tempfile.TemporaryDirectory(prefix="mcfta-shared-prefix-proper-resources-") as directory:
    target = Path(directory) / "OwnAxiomsReport.lean"
    target.write_bytes(report)
    command = shlex.join(
        ["lake", "env", "lean", "-j1", "-DwarningAsError=true", str(target)]
    )
    build = shlex.join(["lake", "build", "MicroCFTA.SourcePruningEnumerationSharedPrefixProperResources"])
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
