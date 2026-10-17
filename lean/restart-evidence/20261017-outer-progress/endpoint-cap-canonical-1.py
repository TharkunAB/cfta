"""Check effective cgroup limits before the one canonical target."""
from pathlib import Path
import os

group = next(line.split(":", 2)[2] for line in Path("/proc/self/cgroup").read_text().splitlines() if line.startswith("0::"))
directory = Path("/sys/fs/cgroup") / group.lstrip("/")
for name, expected in [("memory.max", "4294967296"), ("memory.high", "4294967296"), ("memory.swap.max", "0")]:
    actual = (directory / name).read_text().strip()
    print(f"{name}={actual}", flush=True)
    assert actual == expected, (name, actual)
os.execv("/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake", ["lake", "build", "MicroCFTA.SourceCurrentPrimaryEndpointCap"])
