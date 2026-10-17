from pathlib import Path
import datetime
import json
import os
import re
import subprocess
import sys
here = Path(__file__).resolve().parent
name, *targets = sys.argv[1:]
script = here / (name + ".sh")
assert not script.exists()
script.write_text("#!/bin/bash\nset -euo pipefail\ncontrol=$(cut -d: -f3 /proc/self/cgroup)\nfor key in memory.max memory.high memory.swap.max; do cat \"/sys/fs/cgroup${control}/${key}\"; done\nexec /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d /home/tritlo/Code/mcfta/lean build " + " ".join(targets) + "\n")
env = os.environ.copy()
env.update(XDG_RUNTIME_DIR="/run/user/1000", DBUS_SESSION_BUS_ADDRESS="unix:path=/run/user/1000/bus", HEAVY_PEAKS=str(here / "candidate-peaks.txt"))
started = datetime.datetime.now().astimezone().isoformat()
command = ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m", "bash", str(script)]
with (here / (name + ".log")).open("xb") as out:
    done = subprocess.run(command, env=env, cwd="/home/tritlo/Code/mcfta/lean", stdout=out, stderr=subprocess.STDOUT)
log = (here / (name + ".log")).read_text()
jobs = re.search(r"Build completed successfully \((\d+) jobs\)", log)
(here / (name + ".json")).write_text(json.dumps(dict(started=started, finished=datetime.datetime.now().astimezone().isoformat(), command=command, targets=targets, exit=done.returncode, jobs=int(jobs.group(1)) if jobs else None), indent=2) + "\n")
print(name, "exit",done.returncode,"jobs", jobs.group(1) if jobs else "unknown")
if done.returncode: print(log[-10000:])
sys.exit(done.returncode)
