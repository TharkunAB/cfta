from pathlib import Path
import json,subprocess,sys
area=Path('/tmp/mcfta-recursive-output-20261027')
steps=[('strict', 'strict-output-rendering-1', 'SourceFlatPruningRecursiveOutputRendering'), ('lake', 'build-output-rendering', 'MicroCFTA.SourceFlatPruningRecursiveOutputRendering'), ('strict', 'strict-output-completion-1', 'SourceFlatPruningRecursiveOutputCompletion'), ('lake', 'build-output-completion', 'MicroCFTA.SourceFlatPruningRecursiveOutputCompletion')]
records=[]
for args in steps:
 code=subprocess.run([sys.executable,str(area/"check.py"),*args]).returncode
 records.append({"args":args,"exit_code":code})
 (area/"output-chain-results.json").write_text(json.dumps(records,indent=2)+"\n")
 if code:raise SystemExit(code)
