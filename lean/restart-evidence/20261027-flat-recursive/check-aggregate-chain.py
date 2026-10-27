from pathlib import Path
import json,subprocess,sys
area=Path('/tmp/mcfta-flat-recursive-20261027')
steps=[('lake', 'build-aggregate', 'MicroCFTA.Audit'), ('strict', 'strict-audit-1', 'Audit'), ('public', 'public-readback')]
records=[]
for args in steps:
 code=subprocess.run([sys.executable,str(area/"check.py"),*args]).returncode
 records.append({"args":args,"exit_code":code})
 (area/"aggregate-chain-results.json").write_text(json.dumps(records,indent=2)+"\n")
 if code:raise SystemExit(code)
