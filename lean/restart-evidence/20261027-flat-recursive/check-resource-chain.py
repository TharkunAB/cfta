from pathlib import Path
import json,subprocess,sys
area=Path('/tmp/mcfta-flat-recursive-20261027')
steps=[]
for label,module in [('finite-contract','SourceFlatPruningFiniteContract'),('finite-callback','SourceFlatPruningRecursiveCallbackResources'),('finite-receipt','SourceFlatPruningRecursiveReceiptResources'),('finite-head','SourceFlatPruningRecursiveHeadResources'),('continuation-head','SourceFlatPruningContinuationHead')]:
 steps += [('strict','strict-'+label+'-1',module),('lake','build-'+label,'MicroCFTA.'+module)]
records=[]
for args in steps:
 code=subprocess.run([sys.executable,str(area/'check.py'),*args]).returncode
 records.append({'args':args,'exit_code':code})
 (area/'resource-chain-results.json').write_text(json.dumps(records,indent=2)+'\n')
 if code:raise SystemExit(code)
