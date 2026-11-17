from pathlib import Path
import json
import os
import subprocess
import sys

runtime = Path(__file__).resolve().parent
objects = Path(json.loads((runtime / 'objects.json').read_text())['path'])
module = sys.argv[1]
environment = dict(os.environ)
environment['LEAN_PATH'] = str(objects) + os.pathsep + environment.get('LEAN_PATH', '')
subprocess.run(['lean', '-j1', '-DwarningAsError=true', '-R', str(runtime / 'source'),
    '-o', str(objects / 'MicroCFTA' / (module + '.olean')),
    str(runtime / 'source/MicroCFTA' / (module + '.lean'))], env=environment, check=True)
