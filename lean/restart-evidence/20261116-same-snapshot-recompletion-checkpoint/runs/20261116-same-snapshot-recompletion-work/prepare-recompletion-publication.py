from pathlib import Path
import ast
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
private = base / '20261116-qualified-arrow-and-actual-monotone-finalizer-check'
checked = json.loads((private / 'checked.json').read_text())
assert all(checked['passed']) and len(checked['checks']) == 3
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
previous = base / '20261116-full-outer-and-fragment-producer-publication'
old = base / '20261116-outer-history-and-child-avoidance-checkpoint'
old_pins = json.loads(gzip.decompress((old / 'source-pins.json.gz').read_bytes()))
for name, digest in old_pins.items():
    assert sha(root / name) == digest, name
specs = [
    ('EnumerationPendingAssignmentCongruence', '20261116-current-pending-evaluator-closed-set-congruence-draft', '867da07cb60bf8b6392496d669b06f8a98f3c1ebfedad1042267c085c9fc6147'),
    ('EnumerationPendingAssignmentFixedPoint', '20261116-current-pending-evaluator-stored-equations-fixed-point-draft', '53ee2b8e01a669eccc966b2ec744733539e329341c231cf4ff9d80b258ac7536'),
    ('EnumerationPendingEvaluationWitness', '20261116-current-pending-evaluation-explicit-witness-draft', 'd3fde5b55ba9126ff73a310a17102bcaf00934138aff7315ef753a9f1509b756'),
    ('EnumerationStratifiedLevelReceipts', '20261116-local-stratified-level-receipts-draft', '300dee737eae62fc0bee7fe816b9c8fa6e1f0a5e8083ea77799d0085776c527c'),
    ('EnumerationPendingRecompletion', '20261116-current-snapshot-recompletion-algebra-binder-repair', '5cfea72aacc3ca1418afbeb6fee805067ed32d61acb0ee4dad20e722e816fae1'),
    ('EnumerationStratifiedAllocatedMonotonicity', '20261116-stratified-allocated-level-monotonicity-draft', '1fe1d40e5a75a73a55eba79dc89c5fd58cc34399f608b2bed9cdad1366bdd90b'),
    ('SourcePruningEnumerationParametricArrowBucketWitness', '20261116-parametric-arrow-bucket-recompletion-draft', '917fef0f3ede719fe853654687994298b062a5e4607998e14eec535cb58b1b9d'),
    ('SourcePruningEnumerationArrowBucketRecompletion', '20261116-final-snapshot-arrow-bucket-recompletion-hole-qualification-repair', 'da07d06cf34ab8348049579f70de93e5dcadbea79f22d972fca18c8ed72f1a40'),
]
imports = b''.join(('import MicroCFTA.' + name + '\n').encode() for name, _, _ in specs)
public_probes = b'\n'.join((base / packet / 'PROBES.lean.txt').read_bytes() for _, packet, _ in specs)
assert public_probes.count(b'#print axioms ') == 10
for name, packet, digest in specs:
    source = base / packet / (name + '.lean')
    assert sha(source) == digest
    target = root / 'lean/MicroCFTA' / source.name
    if target.exists():
        assert target.read_bytes() == source.read_bytes()
    else:
        target.write_bytes(source.read_bytes())
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit = root / 'lean/MicroCFTA/Audit.lean'
owner_before = owner.read_bytes()
audit_before = audit.read_bytes()
assert sha(owner) == '6baeb7f22592dc649710880135d93be3e36f47fee5abe30193f4fbb7cee4c2f4'
assert sha(audit) == '3b5793a38a9fd071b8607c8fa526e80e2b7cc8740ac64c6db8dcdbf8e543c7c8'
packets = [base / '20261116-actual-child-finalizer-stratified-cut-draft',
           base / '20261116-actual-child-finalizer-stratified-monotone-cut-draft']
owner_imports = b'import MicroCFTA.EnumerationStratifiedLevelReceipts\nimport MicroCFTA.EnumerationStratifiedAllocatedMonotonicity\n'
new_owner = owner_imports + owner_before + b''.join(b'\n' + (p / 'APPEND.lean.txt').read_bytes() for p in packets)
new_private_probes = b'\n'.join((p / 'PROBES.lean.txt').read_bytes() for p in packets)
assert new_private_probes.count(b'#print axioms ') == 2
assert (private / 'source/MicroCFTA' / owner.name).read_bytes() == new_owner + b'\n' + new_private_probes
resource_probes = (previous / 'ResourceProbes176.lean.txt').read_bytes() + b'\n' + new_private_probes
assert resource_probes.count(b'#print axioms ') == 178
runtime = base / '20261116-same-snapshot-recompletion-publication'
runtime.mkdir()
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(owner_before)
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(audit_before)
(runtime / 'selection.json').write_text(json.dumps(specs, indent=2) + '\n')
owner.write_bytes(new_owner)
audit.write_bytes(imports + audit_before + b'\n' + public_probes)
assert owner.read_bytes().split(b'\n', 2)[2].startswith(owner_before)
assert audit.read_bytes().split(b'\n', 8)[8].startswith(audit_before)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6181
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5181
assert audit.read_bytes().count(b'#print axioms ') == 530
objects = Path(tempfile.mkdtemp(prefix='mcfta-same-snapshot-recompletion-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'ResourceProbes178.lean.txt').write_bytes(resource_probes)
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
assert independent.read_bytes().count(b'#print axioms ') == 125
template = (private / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [
    ('public-build', 'exec lake build', 0),
    ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 178),
    ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 125),
    ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
    ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 530),
]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and (not job[2] or c['total_axiom_reports'] == job[2])
           for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'checks': checks, 'source_pins_unchanged': True, 'source_files': 6181,
          'direct_audit_imports': 5181, 'individual_reports': 530, 'independent_reports': 125,
          'owner_resource_probes': 178, 'original_resource_probes': 136, 'additional_resource_probes': 42,
          'audited_theorems': int(match.group(1)), 'new_modules': 8, 'new_public_theorems': 10,
          'same_snapshot_arrow_recompletion_conditional_proved': True,
          'actual_finalizer_chosen_level_cut_and_allocated_monotonicity_proved': True,
          'outer_depth_history_proved': True, 'original906_public_statement_proved': True,
          'whole_worker_cut_proved': False, 'all_native_domains_and_guards_preserved': False,
          'joint_finite_completion_proved': False, 'all_removed_history_joint_proved': False,
          'haskell_changed': False, 'limits': limits,
          'at': datetime.datetime.now().astimezone().isoformat()}
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [source, runtime / 'ResourceProbes178.lean.txt', strict, independent, runtime / 'selection.json', runtime / 'check.py', Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'resource_reports': 178, 'independent_reports': 125, 'audit_reports': 530}))
