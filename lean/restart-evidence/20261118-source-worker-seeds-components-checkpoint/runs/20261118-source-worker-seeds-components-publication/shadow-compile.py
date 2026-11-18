from pathlib import Path
import json
import os
import subprocess
import sys

runtime = Path(__file__).resolve().parent
selection = json.loads((runtime / 'INHERITANCE-SELECTION.json').read_text())
objects = Path(json.loads((runtime / 'objects.json').read_text())['path'])
module = sys.argv[1]
environment = dict(os.environ)
environment['LEAN_PATH'] = str(objects) + os.pathsep + environment.get('LEAN_PATH', '')
environment['LEAN_NUM_THREADS'] = '1'
if module == '--public-probes':
    subprocess.run(['lean', '-j1', '-DwarningAsError=true',
        str(runtime / 'FreshPublicProbes.lean')], env=environment, check=True)
else:
    assert module in selection['compile_order']
    output = objects / 'MicroCFTA' / (module + '.olean')
    assert not output.is_symlink(), 'A candidate output must not link to a normal cache object.'
    assert not output.exists(), 'Use a fresh runtime for each check.'
    subprocess.run([
        'lean', '-j1', '-DwarningAsError=true', '-R', str(runtime / 'source'),
        '-o', str(output), str(runtime / 'source/MicroCFTA' / (module + '.lean')),
    ], env=environment, check=True)
