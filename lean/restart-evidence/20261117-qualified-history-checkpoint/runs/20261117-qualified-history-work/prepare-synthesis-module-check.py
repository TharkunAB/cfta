from pathlib import Path
import hashlib
import json
import re
import shlex
import sys
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
packet_name, module_name, expected_sha, run_name = sys.argv[1:]
assert re.fullmatch(r'2026[0-9]{4}-[a-z0-9-]+', packet_name)
assert re.fullmatch(r'2026[0-9]{4}-[a-z0-9-]+', run_name)
assert re.fullmatch(r'(?:SourcePruningEnumeration[A-Za-z]+|SourceSynthesisCurrentUniverseLeafInvocationType)', module_name)
packet, run = base / packet_name, base / run_name
run.mkdir()
sha = lambda data: hashlib.sha256(data).hexdigest()
if (packet / 'MANIFEST.sha256').exists():
    for line in (packet / 'MANIFEST.sha256').read_text().splitlines():
        digest, name = line.split(None, 1)
        assert sha((packet / name.strip().lstrip('*')).read_bytes()) == digest, name
else:
    manifest_path = packet / 'MANIFEST.json'
    if not manifest_path.exists():
        manifest_path = packet / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    for name, item in manifest['files'].items():
        digest = item['sha256'] if isinstance(item, dict) else item
        data = (packet / name).read_bytes()
        assert sha(data) == digest, name
        if isinstance(item, dict):
            assert len(data) == item['bytes'], name
raw = (packet / (module_name + '.lean')).read_bytes()
assert sha(raw) == expected_sha
assert b'set_option maxHeartbeats' not in raw, 'Keep the original default limits.'
probes = (packet / 'PROBES.lean.txt').read_bytes()
count = probes.count(b'#print axioms ')
assert count > 0
source = run / 'source/MicroCFTA' / (module_name + '.lean')
source.parent.mkdir(parents=True)
source.write_bytes(raw + b'\n' + probes)
objects = Path(tempfile.mkdtemp(prefix='mcfta-causal-normal-module-'))
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
imports = sorted({line.split()[1] for line in raw.decode().splitlines() if line.startswith('import ')})
assert all(re.fullmatch(r'MicroCFTA\.[A-Za-z0-9_.]+', name) for name in imports)
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(objects / (module_name + '.olean'))) + ' ' + shlex.quote(str(source))
jobs = [('public-dependencies', 'exec lake build ' + ' '.join(imports), 0), ('normal-module', command, count)]
template = (base / '20261116-row-and-scan-block-proof-repair-check/check.py').read_text()
driver = template[:template.index('\njobs =')]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
passed = [c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
          and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs)]
report = {'checks': checks, 'passed': passed, 'source_pins_unchanged': True,
          'normal_module_checked': all(passed), 'proof_limits': 'unchanged defaults',
          'every_causal_historical_event_attached_proved': False, 'joint_finite_completion_proved': False,
          'haskell_changed': False, 'limits': limits}
(runtime / 'results.json').write_text(json.dumps(report, indent=2) + '\\n')
assert len(checks) == 2 and all(passed)
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(run / 'check.py').write_text(driver)
(run / 'selection.json').write_text(json.dumps({'packet': packet_name, 'module': module_name,
    'sha256': expected_sha, 'count': count, 'normal_imports_only': True}, indent=2) + '\n')
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in packet.iterdir() if p.is_file()]
files += [Path(__file__), source, run / 'check.py', run / 'selection.json']
(run / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes()) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(run), 'objects': str(objects), 'reports': count}))
