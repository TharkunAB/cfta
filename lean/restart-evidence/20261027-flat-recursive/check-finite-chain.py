from pathlib import Path
import json,subprocess,sys
area=Path('/tmp/mcfta-flat-recursive-20261027')
steps=[('lake', 'build-finite-ordinary', 'MicroCFTA.SourceFlatPruningRecursiveOrdinaryResources'), ('strict', 'strict-finite-ordinary-forecast-1', 'SourceFlatPruningRecursiveOrdinaryForecastResources'), ('lake', 'build-finite-ordinary-forecast', 'MicroCFTA.SourceFlatPruningRecursiveOrdinaryForecastResources'), ('strict', 'strict-finite-prefix-shape-1', 'SourceFlatPruningRecursivePrefixShape'), ('lake', 'build-finite-prefix-shape', 'MicroCFTA.SourceFlatPruningRecursivePrefixShape'), ('strict', 'strict-finite-parked-1', 'SourceFlatPruningRecursiveParkedResources'), ('lake', 'build-finite-parked', 'MicroCFTA.SourceFlatPruningRecursiveParkedResources'), ('strict', 'strict-finite-expansion-1', 'SourceFlatPruningRecursiveExpansionResources'), ('lake', 'build-finite-expansion', 'MicroCFTA.SourceFlatPruningRecursiveExpansionResources'), ('strict', 'strict-finite-run-step-1', 'SourceFlatPruningRecursiveRunStep'), ('lake', 'build-finite-run-step', 'MicroCFTA.SourceFlatPruningRecursiveRunStep'), ('strict', 'strict-finite-resources-1', 'SourceFlatPruningRecursiveFiniteResources'), ('lake', 'build-finite-resources', 'MicroCFTA.SourceFlatPruningRecursiveFiniteResources')]
records=[]
for args in steps:
 code=subprocess.run([sys.executable,str(area/"check.py"),*args]).returncode
 records.append({"args":args,"exit_code":code})
 (area/"finite-chain-results.json").write_text(json.dumps(records,indent=2)+"\n")
 if code:raise SystemExit(code)
