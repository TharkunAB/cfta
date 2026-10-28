import json,subprocess,sys
from pathlib import Path
a=Path("/tmp/mcfta-prepared-induction-20261028")
for args in json.loads((a/sys.argv[1]).read_text()):
 result=subprocess.run([sys.executable,str(a/"check-installed.py"),*args])
 if result.returncode:raise SystemExit(result.returncode)
