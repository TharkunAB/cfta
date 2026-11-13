"""Replay and check the private application-read observer in the project Nix shell."""
from pathlib import Path
import hashlib
import json
import os
import re
import shlex
import subprocess
import tempfile

packet = Path(__file__).resolve().parent
root = packet.parents[2]
history = json.loads((packet / 'source-history.json').read_text())
source = (packet / 'source.lean.txt').read_bytes()
sha = lambda data: hashlib.sha256(data).hexdigest()
assert sha(source) == history['source_sha256']
assert sha(history['header'].encode()) == history['header_sha256']
assert history['header'].rstrip('\n') + ' := by\n' in source.decode()
states = {'checked59': source}
for step in history['patches']:
    assert sha(step['patch'].encode()) == step['sha256']
    with tempfile.TemporaryDirectory(prefix='mcfta-app-marker-history-') as directory:
        target = Path(directory) / 'Source.lean'
        target.write_bytes(states[step['from']])
        result = subprocess.run(['patch', '--batch', '--fuzz=0', '-p0'], cwd=directory,
                                input=step['patch'], capture_output=True, text=True)
        assert result.returncode == 0, result.stdout + result.stderr
        states[step['to']] = target.read_bytes()
        assert sha(states[step['to']]) == history['stages'][step['to']]['sha256']
assert len(history['patches']) == history['actual_gnu_zero_context_replays'] == 4
for name, expected in history['source_pins'].items():
    assert sha((root / name).read_bytes()) == expected, name
group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
limits = {name: (cgroup / name).read_text().strip()
          for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
ending = 'end MicroCFTA.SourceSynthesisActualAppMarkerSubtrace\n'
body = source.decode()
assert body.count(ending) == 1
body = body.replace(ending, '#check actual_app_marker_function_subtrace\n#print axioms actual_app_marker_function_subtrace\n\n' + ending)
environment = dict(os.environ)
environment.pop('LEAN_SYSROOT', None)
environment['LEAN_NUM_THREADS'] = '1'
with tempfile.TemporaryDirectory(prefix='mcfta-app-marker-private-axioms-') as directory:
    target = Path(directory) / 'PrivateAxioms.lean'
    target.write_text(body)
    command = shlex.join(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', str(target)])
    result = subprocess.run(['nix-shell', str(root / 'shell.nix'), '--run', 'exec ' + command],
                            cwd=root / 'lean', env=environment, capture_output=True, text=True, timeout=300)
if result.returncode:
    print(result.stdout + result.stderr)
    raise SystemExit(result.returncode)
reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)
assert len(reports) == 1, result.stdout
name, dependencies = reports[0]
assert name.endswith('.actual_app_marker_function_subtrace')
axioms = [part.strip() for part in dependencies.split(',') if part.strip()]
assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert (packet / 'source.lean.txt').read_bytes() == source
print(json.dumps({'compiler_exit': 0, 'source_sha256': sha(source), 'private_laws': 1,
                  'public_laws_added': 0, 'axioms': axioms, 'limits': limits,
                  'actual_source_replays': 4, 'identity_row_type_receipt_open': True,
                  'live_library_changes': False, 'haskell_changes': False}, indent=2))
