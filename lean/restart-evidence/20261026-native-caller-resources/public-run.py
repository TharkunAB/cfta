import json, subprocess, sys
from pathlib import Path
area=Path('/tmp/mcfta-native-caller-resources-20261026')
declarations=json.loads((area/'public-declarations.json').read_text())
raise SystemExit(subprocess.run([sys.executable,str(area/'check.py'),'public','public-final-1',*declarations]).returncode)
