from pathlib import Path
import ast
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
private = base / '20261116-full-outer-expanded-birth-and-actual-kept-qualified-check'
checked = json.loads((private / 'checked.json').read_text())
assert len(checked['checks']) == 2 and all(checked['passed'])
previous = base / '20261116-same-snapshot-recompletion-publication'
old = base / '20261116-same-snapshot-recompletion-checkpoint'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
old_pins = json.loads(gzip.decompress((old / 'source-pins.json.gz').read_bytes()))
for name, digest in old_pins.items():
    assert sha(root / name) == digest, name
specs = [
    ('EnumerationExpandedBirthHistory', '20261116-current-expanded-birth-history-typed-definition-repair', '6e90526286544a6388b43b7b5ea1805b11c9662faa3e0afc60c44c78fd9e6442'),
    ('EnumerationExpandedBirthKeptSet', '20261116-expanded-birth-direct-kept-set-draft', '6c8e54f1a8e452bab19a9e86644111dba1a8ed02e1ae57cc2c99579ea7bfec25'),
    ('SourcePruningEnumerationPrefixExpandedBirthHistory', '20261116-prefix-expanded-birth-history-draft', '9fcaf9929fe69cb7caf92b81a37400ddf7eab129eb203f9a19f07c4a4d6ae65d'),
]
imports = b''.join(('import MicroCFTA.' + name + '\n').encode() for name, _, _ in specs)
public_probes = b'\n'.join((base / folder / 'PROBES.lean.txt').read_bytes() for _, folder, _ in specs)
assert public_probes.count(b'#print axioms ') == 7
for name, folder, digest in specs:
    source = base / folder / (name + '.lean')
    assert sha(source) == digest
    assert (root / 'lean/MicroCFTA' / source.name).read_bytes() == source.read_bytes()
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit = root / 'lean/MicroCFTA/Audit.lean'
owner_before = owner.read_bytes()
audit_before = audit.read_bytes()
assert sha(owner) == 'd4dba9e0a86c4b5fe8d69e379aebe4614da5bb99d8d1d1bfe7c87e4544fe94e6'
selection = json.loads((private / 'selection.json').read_text())
appendices = []
new_probes = b''
for folder, digest in selection:
    packet = base / folder
    assert sha(packet / 'APPEND.lean.txt') == digest
    appendices.append((packet / 'APPEND.lean.txt').read_bytes())
    new_probes += b'\n' + (packet / 'PROBES.lean.txt').read_bytes()
assert new_probes.count(b'#print axioms ') == 29
new_owner = imports + owner_before + b''.join(b'\n' + part for part in appendices)
assert (private / 'source/MicroCFTA' / owner.name).read_bytes() == new_owner + b'\n' + new_probes
public_source_probes = (base / selection[-1][0] / 'PROBES.lean.txt').read_bytes()
assert public_source_probes.count(b'#print axioms ') == 2
public_probes += b'\n' + public_source_probes
assert public_probes.count(b'#print axioms ') == 9
resource_probes = (previous / 'ResourceProbes178.lean.txt').read_bytes() + b'\n' + new_probes
assert resource_probes.count(b'#print axioms ') == 207
runtime = base / '20261116-expanded-birth-and-actual-kept-publication'
runtime.mkdir()
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(owner_before)
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(audit_before)
(runtime / 'selection.json').write_text(json.dumps(specs, indent=2) + '\n')
owner.write_bytes(new_owner)
audit.write_bytes(imports + audit_before + b'\n' + public_probes)
assert owner.read_bytes().split(b'\n', 3)[3].startswith(owner_before)
assert audit.read_bytes().split(b'\n', 3)[3].startswith(audit_before)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6184
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5184
assert audit.read_bytes().count(b'#print axioms ') == 539
objects = Path(tempfile.mkdtemp(prefix='mcfta-expanded-birth-kept-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'ResourceProbes207.lean.txt').write_bytes(resource_probes)
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes() + b'\n' + resource_probes)
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(x.value for x in tree.body if isinstance(x, ast.Assign)))
for i, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / ('Owner.olean' if i == 0 else Path(command[-1]).stem + '.olean'))
    if i == 0:
        command[command.index('-R') + 1] = str(source.parent.parent)
        command[-1] = str(source)
for name, _, _ in specs:
    commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o', str(objects / (name + '.olean')), str(root / 'lean/MicroCFTA' / (name + '.lean'))])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(imports + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + public_probes)
assert independent.read_bytes().count(b'#print axioms ') == 134
template = (private / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [
    ('public-build', 'exec lake build', 0),
    ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 207),
    ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 134),
    ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
    ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 539),
]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and (not job[2] or c['total_axiom_reports'] == job[2])
           for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'checks': checks, 'source_pins_unchanged': True, 'source_files': 6184,
          'direct_audit_imports': 5184, 'individual_reports': 539, 'independent_reports': 134,
          'owner_resource_probes': 207, 'original_resource_probes': 136, 'additional_resource_probes': 71,
          'audited_theorems': int(match.group(1)), 'new_modules': 3, 'new_public_theorems': 9,
          'genuine_inner_task_work_birth_induction_proved': True,
          'outer_depth_strong_birth_proved': True,
          'actual_source_pending_bucket_dependency_closure_proved': True,
          'original906_public_statement_proved': True,
          'historical_removed_bucket_occurrence_transport_proved': False,
          'current_native_domains_and_guards_preserved_by_recompletion': False,
          'joint_finite_completion_proved': False, 'all_removed_history_joint_proved': False,
          'haskell_changed': False, 'limits': limits,
          'at': datetime.datetime.now().astimezone().isoformat()}
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [source, runtime / 'ResourceProbes207.lean.txt', strict, independent, runtime / 'selection.json', runtime / 'check.py', Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'resource_reports': 207, 'independent_reports': 134, 'audit_reports': 539}))
