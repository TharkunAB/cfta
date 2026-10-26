from pathlib import Path
import json,subprocess,sys
area=Path('/tmp/mcfta-native-traversal-resources-20261026')
raise SystemExit(subprocess.run([sys.executable,str(area/'check.py'),'public','public-final-1',*json.loads((area/'public-declarations.json').read_text())]).returncode)
