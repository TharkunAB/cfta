from pathlib import Path
import ast
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
private = base / '20261116-full-outer-held-history-final-case-check'
checked = json.loads((private / 'checked.json').read_text())
assert all(checked['passed']) and len(checked['checks']) == 3
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
old = base / '20261116-scoped-history-checkpoint'
old_pins = json.loads(gzip.decompress((old / 'source-pins.json.gz').read_bytes()))
for name, digest in old_pins.items():
    if name != 'lean/MicroCFTA/Audit.lean':
        assert sha(root / name) == digest, name

owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit = root / 'lean/MicroCFTA/Audit.lean'
prefix_name = 'SourcePruningEnumerationPrefixHeldHistoryAtOriginalBudget'
prefix_packet = base / '20261116-current-real-prefix-held-fragment-history-compose-repair'
prefix = prefix_packet / (prefix_name + '.lean')
assert sha(prefix) == '5803fed477359f4129cded2294e58b0792c5081a3d08ff39184b0bee961ddb5f'
prefix_target = root / 'lean/MicroCFTA' / prefix.name
assert prefix_target.read_bytes() == prefix.read_bytes()
owner_before = owner.read_bytes()
audit_before = audit.read_bytes()
parts = [(x['folder'], x['sha256']) for x in json.loads((private / 'selection.json').read_text())]
appendices = []
probes = (base / '20261116-scoped-history-publication/ResourceProbesWithScopedHistory165.lean.txt').read_bytes()
for folder, digest in parts:
    packet = base / folder
    assert sha(packet / 'APPEND.lean.txt') == digest
    appendices.append((packet / 'APPEND.lean.txt').read_bytes())
    probes += b'\n' + (packet / 'PROBES.lean.txt').read_bytes()
assert probes.count(b'#print axioms ') == 175
runtime = base / '20261116-full-outer-held-history-publication'
runtime.mkdir()
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(owner_before)
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(audit_before)
new_import = ('import MicroCFTA.' + prefix_name + '\n').encode()
new_owner = new_import + owner_before + b'\nsection\nset_option maxHeartbeats 2000000\n' + b''.join(b'\n' + part for part in appendices) + b'\nend\n'
full_probes = b''.join(b'\n' + (base / folder / 'PROBES.lean.txt').read_bytes() for folder, _ in parts)
assert (private / 'source/full-outer-chain-and-original906/MicroCFTA' / owner.name).read_bytes() == new_owner + b'\n' + full_probes
final_probes = (base / parts[-1][0] / 'PROBES.lean.txt').read_bytes()
assert audit_before == new_import + (work / 'BASE-AUDIT.lean.txt').read_bytes() + b'\n' + (prefix_packet / 'PROBES.lean.txt').read_bytes()
new_audit = audit_before + b'\n' + final_probes
prefix_target.write_bytes(prefix.read_bytes())
owner.write_bytes(new_owner)
audit.write_bytes(new_audit)
assert owner.read_bytes().split(b'\n', 1)[1].startswith(owner_before)
assert audit.read_bytes().startswith(audit_before)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6172
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5172

objects = Path(tempfile.mkdtemp(prefix='mcfta-full-outer-held-history-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'ResourceProbes175.lean.txt').write_bytes(probes)
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes() + b'\n' + probes)
previous = base / '20261116-scoped-history-publication'
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(x.value for x in tree.body if isinstance(x, ast.Assign)))
for i, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / ('Owner.olean' if i == 0 else Path(command[-1]).stem + '.olean'))
    if i == 0:
        command[command.index('-R') + 1] = str(source.parent.parent)
        command[-1] = str(source)
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o', str(objects / (prefix_name + '.olean')), str(prefix_target)])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(new_import + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + (prefix_packet / 'PROBES.lean.txt').read_bytes() + b'\n' + final_probes)
assert independent.read_bytes().count(b'#print axioms ') == 114
template = (private / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [
    ('public-build', 'exec lake build', 0),
    ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 175),
    ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 114),
    ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
    ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 519),
]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] and (not job[2] or c['total_axiom_reports'] == job[2])
           for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'checks': checks, 'source_pins_unchanged': True, 'source_files': 6172,
          'direct_audit_imports': 5172, 'individual_reports': 519, 'independent_reports': 114,
          'owner_resource_probes': 175, 'original_resource_probes': 136, 'additional_resource_probes': 39,
          'audited_theorems': int(match.group(1)), 'new_public_prefix_history': True, 'new_public_906_header_exact': True,
          'opaque_terminal_history_component': True, 'captured_row_history_component': True,
          'prepared_scan_history_component': True, 'outer_depth_history_proved': True, 'original906_public_statement_proved': True,
          'joint_finite_completion_proved': False, 'haskell_changed': False, 'limits': limits,
          'at': datetime.datetime.now().astimezone().isoformat()}
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [source, runtime / 'ResourceProbes175.lean.txt', strict, independent, runtime / 'check.py', Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'resource_reports': 175, 'independent_reports': 114, 'audit_reports': 519}))
