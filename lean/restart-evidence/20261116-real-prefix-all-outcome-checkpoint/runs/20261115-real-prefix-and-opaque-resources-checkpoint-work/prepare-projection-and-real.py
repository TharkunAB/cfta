from pathlib import Path
import ast
import hashlib
import json
import shlex
import shutil
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
worker = base / '20261115-current-any-budget-identity-advance-projection-repair'
prior = base / '20261115-current-any-budget-identity-component-repair'
for name in ['PUBLIC-HEADER.lean.txt', 'INTERNAL-HEADER.lean.txt', 'PREPARED-HEADER.lean.txt',
             'CONTROL-HEADER.lean.txt', 'SUCCESS-HEADER.lean.txt', 'EMPTY-HEADER.lean.txt',
             'PROBES.lean.txt', 'ORIGINAL-PUBLIC-DECLARATION.lean.txt']:
    assert (worker / name).read_bytes() == (prior / name).read_bytes(), name
raw = (worker / 'APPEND.lean.txt').read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'feb8657c0340e99d74ef4aea7a0ff1cf68290f58d0589880578666fec5f8b04e'
bundle = base / '20261115-current-any-budget-identity-projection-resource-bundle'
bundle.mkdir()
(bundle / 'APPEND.lean.txt').write_bytes(raw)
probes = (base / '20261115-current-any-budget-identity-component-resource-bundle/PROBES.lean.txt').read_bytes()
probes += b'\n' + (worker / 'PROJECTION-PROBES.lean.txt').read_bytes()
(bundle / 'PROBES.lean.txt').write_bytes(probes)
shutil.copyfile(worker / 'IMPORTS.lean.txt', bundle / 'DEPENDENCY-IMPORTS.lean.txt')
run = base / '20261115-native-worker-projection-and-real-resources-check'
subprocess.run(['python3', str(Path(__file__).parent / 'prepare-consumer.py'),
    '--run', run.name, '--dependency-imports', str(bundle / 'DEPENDENCY-IMPORTS.lean.txt'),
    '--spec', bundle.name + ':APPEND.lean.txt:PROBES.lean.txt'], check=True)
driver = run / 'check.py'
text = driver.read_text()
start = text.index('jobs = ')
end = text.index('\nfor name, command, count in jobs:', start)
jobs = ast.literal_eval(text[start + len('jobs = '):end])
objects = Path(shlex.split(jobs[1][1])[shlex.split(jobs[1][1]).index('-o') + 1]).parents[2]
real = base / '20261115-current-real-prefix-all-outcome-resources-draft'
source = run / 'real-source/MicroCFTA/SourcePruningEnumerationRealPrefixAllResources.lean'
source.parent.mkdir(parents=True)
source.write_bytes((real / source.name).read_bytes() + b'\n' + (real / 'PROBES.lean.txt').read_bytes())
modules = [line.split()[1] for line in (real / source.name).read_text().splitlines() if line.startswith('import ')]
jobs[0] = (jobs[0][0], jobs[0][1] + ''.join(' ' + shlex.quote(m) for m in modules), 0)
output = objects / 'real-resources.olean'
command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
command += ' -o ' + shlex.quote(str(output)) + ' ' + shlex.quote(str(source))
jobs.append(('real-prefix-all-outcome-resources', command, (real / 'PROBES.lean.txt').read_text().count('#print axioms ')))
driver.write_text(text[:start] + 'jobs = ' + repr(jobs) + text[end:])
pins = json.loads((run / 'source-pins.json').read_text())
for path in [Path(__file__), real / source.name, real / 'PROBES.lean.txt', source, driver]:
    pins[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
(run / 'source-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(bundle / 'COMPONENTS.json').write_text(json.dumps({'source_already_contains_six_task_scan_and_opaque': True,
    'append_only_consumer': True, 'original_headers_unchanged': True,
    'resource_probes': probes.count(b'#print axioms '), 'raw_sha256': hashlib.sha256(raw).hexdigest()}, indent=2) + '\n')
print(json.dumps({'jobs': len(jobs), 'owner_reports': jobs[1][2], 'real_reports': jobs[2][2], 'objects': str(objects)}))
