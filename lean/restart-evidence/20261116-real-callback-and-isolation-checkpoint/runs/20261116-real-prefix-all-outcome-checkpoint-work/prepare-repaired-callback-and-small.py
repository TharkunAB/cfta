from pathlib import Path
import ast
import hashlib
import json
import shlex
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
run = base / '20261116-native-repaired-callback-isolation-and-small-check'
builder = work / 'prepare-consumer-unique.py'
identity = base / '20261116-current-any-budget-identity-small-unfold-instance-repair'
assert hashlib.sha256((identity / 'APPEND.lean.txt').read_bytes()).hexdigest() == 'ee288450aa98f154d1704bf27b38d592bd8814f85d918743e4a92d4362d0df1f'
subprocess.run(['python3', str(builder), '--run', run.name, '--spec',
    identity.name + ':APPEND.lean.txt:COMPONENT-PROBES.lean.txt'], check=True)
driver = run / 'check.py'
text = driver.read_text()
start = text.index('jobs = ')
end = text.index('\nfor name, command, count in jobs:', start)
jobs = ast.literal_eval(text[start + len('jobs = '):end])
parts = shlex.split(jobs[1][1])
objects = Path(parts[parts.index('-o') + 1]).parents[2]
pins = json.loads((run / 'source-pins.json').read_text())
modules = set()
standalone = []
specs = [
    ('real-callback', '20261116-current-real-worker-callback-let-normalization-repair',
     'SourcePruningEnumerationRealWorkerCallbackResources.lean', 'PROBES.lean.txt',
     '768fbe40721fe95da478eff4ed4258f000b255c8d782d381881afe9bf9e44846'),
    ('earlier-isolation', '20261116-current-real-prefix-earlier-isolated-draft',
     'SourcePruningEnumerationPrefixIsolatedAtOriginalBudget.lean', 'PROBES.lean.txt',
     'ed0cba61f4396a6f9f8fe5ec8b2fb414a6106e4ff13ac89ec46dff690315b276'),
    ('normal-alphabet', identity.name, 'PreparedSeedAlphabetGate.lean',
     'NORMAL-GATE-PROBES.lean.txt', 'aa80762534819d8d17bdd436bf2536eecfddb6bc5ed7430c1d34330989ab6233'),
]
for label, folder, name, probe_name, digest in specs:
    packet = base / folder
    raw, probe = packet / name, packet / probe_name
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    source = run / (label + '-source') / 'MicroCFTA' / name
    source.parent.mkdir(parents=True)
    source.write_bytes(raw.read_bytes() + b'\n' + probe.read_bytes())
    modules.update(line.split()[1] for line in raw.read_text().splitlines() if line.startswith('import '))
    command = 'exec lake env lean -j1 -DwarningAsError=true -R ' + shlex.quote(str(source.parent.parent))
    command += ' -o ' + shlex.quote(str(objects / (label + '.olean'))) + ' ' + shlex.quote(str(source))
    standalone.append((label, command, probe.read_text().count('#print axioms ')))
    for path in [raw, probe, source]:
        pins[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
jobs[0] = (jobs[0][0], jobs[0][1] + ''.join(' ' + shlex.quote(m) for m in sorted(modules)), 0)
jobs = [jobs[0]] + standalone + jobs[1:]
assert len({name for name, _, _ in jobs}) == len(jobs)
driver.write_text(text[:start] + 'jobs = ' + repr(jobs) + text[end:])
for path in [Path(__file__), driver]:
    pins[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
(run / 'source-pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(run / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
print(json.dumps({'jobs': [(n, count) for n, _, count in jobs], 'objects': str(objects)}))
