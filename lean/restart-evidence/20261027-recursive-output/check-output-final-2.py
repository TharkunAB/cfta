from pathlib import Path
import json,subprocess,sys
area=Path('/tmp/mcfta-recursive-output-20261027')
steps=[('strict', 'strict-output-origin-5', 'SourceFlatPruningRecursiveOutputOrigin'), ('lake', 'build-output-origin', 'MicroCFTA.SourceFlatPruningRecursiveOutputOrigin'), ('strict', 'strict-output-resources-4', 'SourceFlatPruningRecursiveOutputResources'), ('lake', 'build-output-resources', 'MicroCFTA.SourceFlatPruningRecursiveOutputResources')]
records=[]
for args in steps:
 code=subprocess.run([sys.executable,str(area/"check.py"),*args]).returncode
 records.append({"args":args,"exit_code":code})
 (area/"output-chain-results.json").write_text(json.dumps(records,indent=2)+"\n")
 if code:raise SystemExit(code)
