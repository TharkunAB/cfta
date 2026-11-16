from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
private = base / '20261116-real-parked-immediate-suffix-kept-check'
checked = json.loads((private / 'checked.json').read_text())
assert len(checked['checks']) == 2 and all(checked['passed'])
for name, digest in json.loads((private / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
previous = base / '20261116-expanded-birth-and-actual-kept-publication'
packet = base / '20261116-real-parked-immediate-suffix-kept-draft'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
raw = (packet / 'APPEND.lean.txt').read_bytes()
assert sha(packet / 'APPEND.lean.txt') == 'c47d185496fe2342fd3b6de4876ca37c34a181d8ef3c5b3ff5219fd7c8683a85'
private_name = b'real_parked_removed_bucket_kept_at_immediate_suffix'
public_name = b'runEager_real_parked_removed_bucket_kept_at_immediate_suffix'
assert raw.count(b'private theorem ' + private_name) == 1
public = raw.replace(b'private theorem ' + private_name, b'theorem ' + public_name)
private_header = (packet / 'PRIVATE-HEADER.lean.txt').read_bytes()
public_header = private_header.replace(b'private theorem ' + private_name, b'theorem ' + public_name)
assert public_header.rstrip() + b' := by' in public
assert public.replace(b'theorem ' + public_name, b'private theorem ' + private_name) == raw
probes = (packet / 'PROBES.lean.txt').read_bytes().replace(private_name, public_name)
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit = root / 'lean/MicroCFTA/Audit.lean'
before = owner.read_bytes()
old_audit = audit.read_bytes()
extra_import = b'import MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs\n'
assert extra_import not in before
new_owner = extra_import + before + b'\n' + public
private_source = private / 'source/MicroCFTA' / owner.name
assert private_source.read_bytes() == extra_import + before + b'\n' + raw + b'\n' + (packet / 'PROBES.lean.txt').read_bytes()
runtime = base / '20261116-immediate-historical-suffix-kept-publication'
runtime.mkdir()
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(before)
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(old_audit)
(runtime / 'PUBLIC-HEADER.lean.txt').write_bytes(public_header)
(runtime / 'PROBES.lean.txt').write_bytes(probes)
(runtime / 'PUBLIC-APPEND.lean.txt').write_bytes(public)
owner.write_bytes(new_owner)
audit.write_bytes(old_audit + b'\n' + probes)
assert owner.read_bytes().split(b'\n', 1)[1].startswith(before)
assert audit.read_bytes().startswith(old_audit)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6185
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5185
assert audit.read_bytes().count(b'#print axioms ') == 541
resources = (previous / 'ResourceProbes207.lean.txt').read_bytes() + b'\n' + probes
assert resources.count(b'#print axioms ') == 208
(runtime / 'ResourceProbes208.lean.txt').write_bytes(resources)
objects = Path(tempfile.mkdtemp(prefix='mcfta-immediate-historical-suffix-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(new_owner + b'\n' + resources)
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(x.value for x in tree.body if isinstance(x, ast.Assign)))
for i, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / ('Owner.olean' if i == 0 else Path(command[-1]).stem + '.olean'))
    if i == 0:
        command[command.index('-R') + 1] = str(source.parent.parent)
        command[-1] = str(source)
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes((previous / 'IndependentProbes.lean').read_bytes() + b'\n' + probes)
assert independent.read_bytes().count(b'#print axioms ') == 136
template = (private / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [
    ('public-build', 'exec lake build', 0),
    ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 208),
    ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 136),
    ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
    ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 541),
]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'checks': checks, 'source_pins_unchanged': True, 'source_files': 6185,
          'direct_audit_imports': 5185, 'individual_reports': 541, 'independent_reports': 136,
          'owner_resource_probes': 208, 'original_resource_probes': 136, 'additional_resource_probes': 72,
          'audited_theorems': int(match.group(1)), 'new_modules': 0, 'new_public_theorems': 1,
          'one_actual_clear_event_same_original_output_kept_proved': True,
          'every_historical_occurrence_attached_proved': False,
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
files += [source, strict, independent, runtime / 'ResourceProbes208.lean.txt', runtime / 'check.py', Path(__file__)]
files += [runtime / name for name in ['PUBLIC-HEADER.lean.txt', 'PROBES.lean.txt', 'PUBLIC-APPEND.lean.txt', 'OWNER-BEFORE.lean.txt', 'AUDIT-BEFORE.lean.txt']]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'resource_reports': 208, 'independent_reports': 136, 'audit_reports': 541, 'public_header_sha256': sha(runtime / 'PUBLIC-HEADER.lean.txt')}))
