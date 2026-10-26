import json, subprocess, sys
from pathlib import Path
area=Path('/tmp/mcfta-native-recursive-hooks-20261026')
subprocess.run([sys.executable,str(area/'check.py'),'public','public-final-1',*json.loads((area/'public-declarations.json').read_text())],check=True)
