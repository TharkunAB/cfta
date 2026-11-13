"""Check source history, public theorem names, and the native witness in Nix."""
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
names = json.loads((packet / 'theorems.json').read_text())
digest = lambda data: hashlib.sha256(data).hexdigest()
sources = {name: (root / path).read_bytes() for name, path in history['seeds'].items()}
for name, data in sources.items():
    assert digest(data) == history['stages'][name]['sha256'], name
for edge in history['patches']:
    assert digest(edge['patch'].encode()) == edge['sha256']
    with tempfile.TemporaryDirectory(prefix='mcfta-native-witness-history-') as directory:
        target = Path(directory) / 'Source.lean'
        target.write_bytes(sources[edge['from']])
        result = subprocess.run(['patch', '--batch', '--fuzz=0', '-p0'], cwd=directory,
                                input=edge['patch'], capture_output=True, text=True)
        assert result.returncode == 0, result.stdout + result.stderr
        sources[edge['to']] = target.read_bytes()
        assert digest(sources[edge['to']]) == history['stages'][edge['to']]['sha256']
assert len(history['patches']) == history['actual_gnu_zero_context_replays'] == 6
for path, expected in history['original_source_pins'].items():
    data = sources['arrow-base'] if path.endswith('/SourceSynthesisGeneralizeFiniteInstances.lean') else (root / path).read_bytes()
    assert digest(data) == expected, path
native = sources['native-public']
assert history['public_header'].rstrip('\n') + ' := by\n' in native.decode()
assert re.findall(r'^theorem (\w+)', native.decode(), re.M) == ['identity_component_native_member']
assert names == ['MicroCFTA.SourceSynthesisGeneralizeFiniteInstances.instantiate_fun',
                 'MicroCFTA.SourceSynthesisCurrentIdentityNativeWitness.identity_component_native_member']
group = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
limits = {name: (cgroup / name).read_text().strip()
          for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
environment = dict(os.environ)
environment.pop('LEAN_SYSROOT', None)
environment['LEAN_NUM_THREADS'] = '1'
report = native + ''.join('\n#check ' + name + '\n#print axioms ' + name + '\n' for name in names).encode()
with tempfile.TemporaryDirectory(prefix='mcfta-native-witness-axioms-') as directory:
    target = Path(directory) / 'Axioms.lean'
    target.write_bytes(report)
    command = 'lake build MicroCFTA.SourceSynthesisCurrentIdentityNativeWitness && exec ' + shlex.join(
        ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', str(target)])
    result = subprocess.run(['nix-shell', str(root / 'shell.nix'), '--run', command],
                            cwd=root / 'lean', env=environment, capture_output=True, text=True, timeout=300)
if result.returncode:
    print(result.stdout + result.stderr)
    raise SystemExit(result.returncode)
axioms = {}
for name in names:
    tail = result.stdout.split("'" + name + "'", 1)[1]
    if tail.startswith(' does not depend on any axioms'):
        axioms[name] = []
    else:
        assert tail.startswith(' depends on axioms: [')
        axioms[name] = [part.strip() for part in tail.split('[', 1)[1].split(']', 1)[0].split(',') if part.strip()]
    assert set(axioms[name]) <= {'propext', 'Classical.choice', 'Quot.sound'}
for name, path in history['seeds'].items():
    assert digest((root / path).read_bytes()) == history['stages'][name]['sha256']
print(json.dumps({'compiler_exit': 0, 'source_sha256': digest(native), 'limits': limits,
                  'axioms': axioms, 'actual_source_replays': 6, 'public_laws_added': 2,
                  'emitted_type_origin_proved': False, 'haskell_changes': False}, indent=2))
