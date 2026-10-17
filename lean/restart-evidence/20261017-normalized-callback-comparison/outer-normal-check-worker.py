from pathlib import Path
import json
import os
import sys
limits, snapshot = sys.argv[1:]
control = next(line.split(":",2)[2] for line in Path("/proc/self/cgroup").read_text().splitlines() if line.startswith("0:"))
base = Path("/sys/fs/cgroup") / control.lstrip("/")
actual = {key: (base / key).read_text().strip() for key in ["memory.max","memory.high","memory.swap.max"]}
actual["cgroup"] = control
Path(limits).write_text(json.dumps(actual, indent=2) + "\n")
assert actual["memory.max"] == "4294967296"
assert actual["memory.high"] == "4294967296"
assert actual["memory.swap.max"] == "0"
lean = "/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
os.execv(lean, [lean,"-Dlinter.all=true",snapshot])
