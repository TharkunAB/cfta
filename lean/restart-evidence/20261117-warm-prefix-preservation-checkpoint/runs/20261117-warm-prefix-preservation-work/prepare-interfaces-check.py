from pathlib import Path
import ast
import hashlib
import json
import shlex
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).resolve().parent
packet = base / '20261117-warm-actual-prefix-returned-interfaces-draft'
runtime = base / '20261117-warm-actual-prefix-interfaces-first-check'
sha = lambda data: hashlib.sha256(data).hexdigest()
assert sha((packet / 'MANIFEST.json').read_bytes()) == 'c86d0d4f0a955f925d49f5983f23079f348bfb93bdfda8d218fe99951acf9114'
manifest = json.loads((packet / 'MANIFEST.json').read_text())
for name, record in manifest['files'].items():
    data = (packet / name).read_bytes()
    assert len(data) == record['bytes'] and sha(data) == record['sha256'], name
for name, record in json.loads((packet / 'SOURCE-PINS.json').read_text()).items():
    data = (root / name).read_bytes()
    assert len(data) == record['bytes'] and sha(data) == record['sha256'], name
layout = json.loads((packet / 'LAYOUT.json').read_text())
components = layout['components']
assert len(components) == 3
assert [item['module'] for item in components] == layout['compile_order']
for item in components:
    old = (packet / item['old_source']).read_bytes()
    raw = (packet / item['normal_source']).read_bytes()
    assert old == (root / 'lean/MicroCFTA' / (item['module'] + '.lean')).read_bytes()
    assert len(old) == item['old_bytes'] and sha(old) == item['old_sha256']
    assert raw.startswith(old) and sha(raw) == item['normal_sha256']
    assert sha((packet / item['append']).read_bytes()) == item['append_sha256']
    assert sha((packet / item['first_header']).read_bytes()) == item['first_header_sha256']
    assert (packet / item['first_header']).read_text().rstrip() in raw.decode()
    assert b'set_option maxHeartbeats' not in (packet / item['append']).read_bytes()
    assert (packet / item['check_append']).read_bytes().count(b'#print axioms ') == 1

runtime.mkdir()
objects = Path(tempfile.mkdtemp(prefix='mcfta-warm-prefix-interface-check-'))
(objects / 'MicroCFTA').mkdir()
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
source_root = runtime / 'source'
(source_root / 'MicroCFTA').mkdir(parents=True)
worker = runtime / 'shadow-compile.py'
worker.write_text('''from pathlib import Path
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
''')
ast.parse(worker.read_text())
jobs = []
for item in components:
    module = item['module']
    source = source_root / 'MicroCFTA' / (module + '.lean')
    source.write_bytes((packet / item['normal_source']).read_bytes()
        + b'\n' + (packet / item['check_append']).read_bytes())
    command = 'exec lake env python3 ' + shlex.quote(str(worker)) + ' ' + shlex.quote(module)
    jobs.append((module, command, 1))
template = (base / '20261117-warm-edge-initial-profile-publication/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx']
    and not item['nonstandard_axioms'] and item['total_axiom_reports'] == 1 for item in checks]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
    'normal_module_checked': all(passed), 'normal_source_changed': False,
    'existing_owner_prefixes_byte_exact': True, 'new_public_reports': 3,
    'same_original_fuels': True, 'proof_limits': 'unchanged defaults for appended proofs',
    'source_semantic_callbacks_proved': False, 'joint_finite_completion_proved': False,
    'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 3 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
ast.parse(driver)
(runtime / 'check.py').write_text(driver)
(runtime / 'selection.json').write_text(json.dumps({'packet': packet.name,
    'manifest_sha256': sha((packet / 'MANIFEST.json').read_bytes()),
    'components': components, 'compile_order': layout['compile_order'],
    'shadow_objects_precede_normal_imports': True,
    'new_public_reports': 3, 'normal_source_changed': False}, indent=2) + '\n')
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / name for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [path for path in packet.iterdir() if path.is_file()]
files += [path for path in runtime.rglob('*') if path.is_file()]
files += [Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps(
    {str(path.relative_to(root)): sha(path.read_bytes()) for path in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'reports': 3,
    'normal_source_changed': False, 'compile_order': layout['compile_order']}))
