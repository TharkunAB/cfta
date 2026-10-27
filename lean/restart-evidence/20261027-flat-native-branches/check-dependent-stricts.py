from pathlib import Path
import json
import subprocess
import sys

area = Path('/tmp/mcfta-flat-native-branches-20261027')
modules = ['SourceFlatPruningNativeBranchCompletion', 'SourceFlatPruningNativeOrdinary',
    'SourceFlatPruningNativeOrdinaryCompletion', 'SourceFlatPruningNativeOrdinaryContinuations']
path = area / 'strict-checks.json'
checks = json.loads(path.read_text())
for module in modules:
    folder = 'strict-final-' + module
    result = subprocess.run([sys.executable, str(area / 'check.py'), 'strict', folder, module])
    if result.returncode:
        raise SystemExit(result.returncode)
    checks[module] = folder
    path.write_text(json.dumps(checks, indent=2) + '\n')
