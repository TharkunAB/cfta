from __future__ import annotations

import datetime
import hashlib
import json
from pathlib import Path
import shlex
import subprocess


def main() -> None:
    packet = Path(__file__).resolve().parent
    root = packet.parents[2]
    snapshots = json.loads((packet / "source-hashes.json").read_text())
    for path, expected in snapshots.items():
        assert hashlib.sha256((root / path).read_bytes()).hexdigest() == expected, path
    group = next(
        line.split(":", 2)[2]
        for line in Path("/proc/self/cgroup").read_text().splitlines()
        if line.startswith("0::")
    )
    current = Path("/sys/fs/cgroup") / group.lstrip("/")
    limits = {
        name: (current / name).read_text().strip()
        for name in ["memory.max", "memory.high", "memory.swap.max"]
    }
    assert limits == {
        "memory.max": "4294967296",
        "memory.high": "4294967296",
        "memory.swap.max": "0",
    }, limits
    expression = (
        "let pkgs=import<nixpkgs>{};in pkgs.mkShell{"
        "inputsFrom=[(import ./shell.nix{inherit pkgs;})];packages=[pkgs.gmp];}"
    )
    commands = [
        ["fourmolu", "--mode", "check", str(packet / "repro.hs")],
        [
            "cabal", "build", "cfta:lib:cfta",
            "--offline", "--disable-optimization", "-j1",
        ],
        [
            "cabal", "exec", "--offline", "--", "runghc-9.14.1",
            "-package-id=cfta-0.1.0.0-inplace",
            str(packet / "repro.hs"),
        ],
    ]
    output = ""
    for command in commands:
        result = subprocess.run(
            ["nix-shell", "-E", expression, "--run", shlex.join(command)],
            cwd=root, capture_output=True, text=True,
        )
        if result.returncode:
            raise RuntimeError((result.stdout + result.stderr)[-6000:])
        output = result.stdout
    assert output == (packet / "expected.txt").read_text(), output
    for path, expected in snapshots.items():
        assert hashlib.sha256((root / path).read_bytes()).hexdigest() == expected, path
    report = {
        "at": datetime.datetime.now().astimezone().isoformat(),
        "source_hashes": snapshots,
        "repro_sha256": hashlib.sha256((packet / "repro.hs").read_bytes()).hexdigest(),
        "limits": limits,
        "commands": commands,
        "observed": output,
        "fixture_same_multiset": True,
        "fixture_eager_count": 4,
        "fixture_shallow_count": 4,
        "ordering_counterexample_reproduced": True,
        "ordered_equivalence": False,
        "runtime_haskell": True,
        "runtime_lean": False,
        "public_program_projection_counterexample": False,
        "production_behavior_bug_established": False,
    }
    (packet / "checked.json").write_text(json.dumps(report, indent=2) + "\n")
    print(output, end="")
    print("Confirmed enumeration order distinction; this is not a production bug.")


if __name__ == "__main__":
    main()
