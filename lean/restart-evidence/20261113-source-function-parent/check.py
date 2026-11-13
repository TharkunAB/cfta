from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shlex
import subprocess
import tempfile
from collections import deque

packet = Path(__file__).resolve().parent
root = packet.parents[2]
manifest = json.loads((packet / "source-history.json").read_text())
allowed = {"propext", "Classical.choice", "Quot.sound"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_tree():
    sources = sorted((root / "lean/MicroCFTA").glob("*.lean"))
    rows = [path.name + " " + digest(path.read_bytes()) for path in sources]
    return len(rows), digest(("\n".join(rows) + "\n").encode())


def check_sources():
    assert source_tree() == (manifest["live_modules"], manifest["source_tree_sha256"])
    for name, expected in manifest["live_sources"].items():
        assert digest((root / name).read_bytes()) == expected, name


group = next(line.split(":", 2)[2] for line in Path("/proc/self/cgroup").read_text().splitlines()
             if line.startswith("0::"))
cgroup = Path("/sys/fs/cgroup") / group.lstrip("/")
limits = {name: (cgroup / name).read_text().strip()
          for name in ["memory.max", "memory.high", "memory.swap.max"]}
assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
check_sources()
environment = dict(os.environ)
environment.pop("LEAN_SYSROOT", None)
environment["LEAN_NUM_THREADS"] = "1"
stages = {}
replays = 0
reports = []

with tempfile.TemporaryDirectory(prefix="mcfta-source-parent-replay-") as temporary:
    work = Path(temporary)
    for family in manifest["families"]:
        base = family["base"]
        if "git_path" in base:
            data = subprocess.check_output(["git", "show", base["commit"] + ":" + base["git_path"]], cwd=root)
        else:
            data = (packet / base["file"]).read_bytes()
        assert digest(data) == base["sha256"], family["name"]
        stages[(family["name"], base["name"])] = data
        destination = work / family["name"] / "source.lean"
        destination.parent.mkdir()
        destination.write_bytes(data)
        for stage in family["stages"]:
            subprocess.run(["patch", "--batch", "--fuzz=0", "--no-backup-if-mismatch",
                            str(destination), str(packet / stage["patch"])],
                           check=True, capture_output=True, text=True)
            data = destination.read_bytes()
            assert digest(data) == stage["sha256"], stage["name"]
            stages[(family["name"], stage["name"])] = data
            replays += 1

    assert len(stages) == manifest["expected_source_stages"]
    assert replays == manifest["expected_zero_context_replays"]
    print(json.dumps({"stage": "source_history_replayed", "source_stages": len(stages),
                      "zero_context_replays": replays, "next": "MicroCFTA.Audit"}), flush=True)
    tail = deque(maxlen=80)
    process = subprocess.Popen(["nix-shell", str(root / "shell.nix"), "--run",
                                "exec lake build MicroCFTA.Audit"], cwd=root / "lean",
                               env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert process.stdout is not None
    lines = 0
    for line in process.stdout:
        tail.append(line)
        lines += 1
    code = process.wait()
    if code:
        print("".join(tail))
        raise SystemExit(code)
    check_sources()
    for number, check in enumerate(manifest["checks"]):
        if "live" in check:
            source = ("import MicroCFTA." + check["live"] + "\n" +
                      "\n".join("#print axioms " + law for law in check["laws"]) + "\n").encode()
        else:
            source = stages[(check["family"], check["stage"])]
            ending = ("end " + check["namespace"] + "\n").encode()
            assert source.count(ending) == 1
            prints = ("\n".join("#print axioms " + law for law in check["laws"]) + "\n\n").encode()
            source = source.replace(ending, prints + ending)
        path = work / ("Check" + str(number) + ".lean")
        path.write_bytes(source)
        command = "exec lake env lean -j1 -DwarningAsError=true " + shlex.quote(str(path))
        checked = subprocess.run(["nix-shell", str(root / "shell.nix"), "--run", command],
                                 cwd=root / "lean", env=environment, capture_output=True, text=True)
        output = checked.stdout + checked.stderr
        if checked.returncode:
            print(output)
            raise SystemExit(checked.returncode)
        dependencies = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output, re.S)
        assert len(dependencies) == len(check["laws"]), output
        names = [sorted(name.strip() for name in row.split(",") if name.strip()) for row in dependencies]
        assert all(set(row) <= allowed for row in names), output
        assert all(law.rsplit(".", 1)[-1] in output for law in check["laws"]), output
        reports.append({"laws": check["laws"], "axioms": names, "compiler_exit": 0})

check_sources()
trace = (root / "lean/.lake/build/lib/lean/MicroCFTA/Audit.trace").read_text()
counts = re.findall(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", trace)
assert counts
report = {"at": datetime.datetime.now().astimezone().isoformat(), "limits": limits,
          "source_tree_sha256": manifest["source_tree_sha256"], "live_modules": manifest["live_modules"],
          "zero_context_replays": replays, "source_stages": len(stages), "audit_exit": 0,
          "audit_output_lines": lines, "audit_axiom_theorems": int(counts[-1]), "checks": reports,
          "current_read_origin_proved": False, "joint_completion_proved": False, "haskell_changes": False}
(packet / "checked.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
