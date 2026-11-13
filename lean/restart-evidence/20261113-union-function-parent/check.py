from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import tempfile

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load_packet(packet):
    return json.loads((packet / "source-history.json").read_text())


def replay(packet, manifest, work):
    assert "GNU" in subprocess.run(["patch", "--version"], capture_output=True,
                                   text=True, check=True).stdout
    stages = {}
    checked = {}
    replays = []

    def apply(raw, patch, destination, expected):
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(raw)
        result = subprocess.run(
            ["patch", "--batch", "--fuzz=0", "--no-backup-if-mismatch", "-p0",
             "-i", str(packet / patch)], cwd=destination.parent,
            capture_output=True, text=True, check=False)
        assert result.returncode == 0, result.stdout + result.stderr
        assert sha(destination.read_bytes()) == expected
        replays.append({"patch": patch, "sha256": expected, "exit": result.returncode})
        return destination

    for family in manifest["families"]:
        name = family["name"]
        base = family["base"]
        raw = (packet / base["file"]).read_bytes()
        assert sha(raw) == base["sha256"]
        destination = work / name / base["name"] / "source.lean"
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(raw)
        stages[name, base["name"]] = destination
        for stage in family["stages"]:
            destination = apply(raw, stage["patch"],
                work / name / stage["name"] / "source.lean", stage["sha256"])
            raw = destination.read_bytes()
            stages[name, stage["name"]] = destination
    assert len(stages) == manifest["expected_source_stages"]
    assert len(replays) == manifest["expected_history_patches"]

    for row in manifest["diagnostics"]:
        key = row["family"], row["stage"]
        raw = stages[key].read_bytes()
        assert sha(raw) == row["raw_sha256"]
        variant = row["checked_variant"]
        if variant is None:
            destination = stages[key]
        elif variant.endswith(".patch"):
            destination = apply(raw, variant,
                work / "instrumented" / row["family"] / row["stage"] / "source.lean",
                row["checked_sha256"])
        else:
            destination = work / "instrumented" / row["family"] / row["stage"] / "source.lean"
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes((packet / variant).read_bytes())
        assert sha(destination.read_bytes()) == row["checked_sha256"]
        checked[key] = destination
    for row in manifest.get("pending_first_filter", []):
        raw = (packet / row["raw_file"]).read_bytes()
        assert sha(raw) == row["raw_sha256"]
        apply(raw, row["checked_patch"], work / "pending" / row["name"] / "source.lean",
              row["checked_sha256"])
        assert row["proof_credit"] is False and row["required_check"] is False
    assert len(replays) == manifest["expected_total_gnu_replays"]
    return stages, checked, replays


def verify_live(root, manifest):
    for relative, expected in manifest["live_sources"].items():
        assert sha((root / relative).read_bytes()) == expected, relative
    aggregate = manifest.get("root_aggregate_pins")
    assert aggregate is not None, "Root must supply the final aggregate pins before compilation."
    sources = sorted((root / "lean/MicroCFTA").glob("*.lean"))
    lines = [p.name + " " + sha(p.read_bytes()) for p in sources]
    assert len(sources) == aggregate["live_modules"]
    assert sha(("\n".join(lines) + "\n").encode()) == aggregate["source_tree_sha256"]


def limits():
    cg = next(line.split(":", 2)[2] for line in Path("/proc/self/cgroup").read_text().splitlines()
              if line.startswith("0::"))
    directory = Path("/sys/fs/cgroup") / cg.lstrip("/")
    actual = {name: (directory / name).read_text().strip()
              for name in ["memory.max", "memory.high", "memory.swap.max"]}
    assert actual == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    return actual


def compile_checks(root, packet, manifest, stages, checked, work, output):
    observed_limits = limits()
    verify_live(root, manifest)
    environment = dict(os.environ)
    environment.pop("LEAN_SYSROOT", None)
    environment["LEAN_NUM_THREADS"] = "1"
    results = []

    def run(name, command, required_axiom_groups=0):
        result = subprocess.run(["nix-shell", str(root / "shell.nix"), "--run", command],
            cwd=root / "lean", env=environment, capture_output=True, text=True, check=False)
        text = result.stdout + result.stderr
        (output / (name + ".txt")).write_text(text)
        groups = [sorted(x.strip() for x in group.split(",") if x.strip())
                  for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", text, re.S)]
        assert result.returncode == 0, name + ": see its exact output log"
        assert "sorryAx" not in text
        assert len(groups) >= required_axiom_groups
        assert all(set(group) <= ALLOWED for group in groups)
        results.append({"name": name, "exit": result.returncode,
                        "axiom_groups": len(groups), "nonstandard_axioms": []})

    run("full-audit-build", "exec lake build MicroCFTA.Audit")
    laws = [
        ("union", "public-334-repaired", "public-union",
         "MicroCFTA.SourceSynthesisCurrentUnionFunctionParent.actual_app_identity_union_function_parent"),
        ("row-growth", "23-public", "public-row-growth",
         "MicroCFTA.SourceCurrentStoredMuRetainedAlignment.RowCall.grows"),
    ]
    for family, stage, name, law in laws:
        path = work / (name + ".lean")
        path.write_bytes(stages[family, stage].read_bytes() +
                         ("\n#check " + law + "\n#print axioms " + law + "\n").encode())
        run(name, "exec lake env lean -j1 -DwarningAsError=true " + shlex.quote(str(path)), 1)
    private = checked["shape", "323-check5"]
    run("private-identity-shape", "exec lake env lean -j1 -DwarningAsError=true " + shlex.quote(str(private)), 1)
    private_prefix = checked["type-prefix", "327-alias"]
    run("private-identity-type-prefix", "exec lake env lean -j1 -DwarningAsError=true " + shlex.quote(str(private_prefix)), 1)
    probe = work / "public-import-check.lean"
    probe.write_bytes((packet / "checks/public.lean.txt").read_bytes())
    run("public-import-check", "exec lake env lean -j1 -DwarningAsError=true " + shlex.quote(str(probe)), 2)
    audit = stages["audit", "4995-current"]
    run("full-audit-strict", "exec lake env lean -j1 -DwarningAsError=true " + shlex.quote(str(audit)), 1)
    verify_live(root, manifest)
    return {"limits": observed_limits, "results": results,
            "compiler_run": True, "worker_or_model_claim_added": False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--repo", type=Path, default=Path("/home/tritlo/Code/mcfta"))
    parser.add_argument("--reconstruct-only", action="store_true")
    args = parser.parse_args()
    packet = args.packet.resolve()
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False)
    manifest = load_packet(packet)
    with tempfile.TemporaryDirectory(prefix="replay-", dir=output) as temporary:
        stages, checked, replays = replay(packet, manifest, Path(temporary))
        report = {"source_stages": len(stages), "gnu_replays": replays,
                  "historical_failed_stages_remain_failed": True, "compiler_run": False}
        (output / "reconstruction.json").write_text(json.dumps(report, indent=2) + "\n")
        if not args.reconstruct_only:
            result = compile_checks(args.repo.resolve(), packet, manifest, stages,
                                    checked, Path(temporary), output)
            (output / "checked.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"out": str(output), "stages": len(stages), "replays": len(replays),
                      "compiler_run": not args.reconstruct_only}))


if __name__ == "__main__":
    main()
