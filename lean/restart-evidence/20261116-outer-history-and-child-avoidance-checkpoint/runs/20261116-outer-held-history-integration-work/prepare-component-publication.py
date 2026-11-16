from pathlib import Path
import ast
import gzip
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
private = base / '20261116-prefix-opaque-and-row-held-history-check'
checked = json.loads((private / 'checked.json').read_text())
assert all(checked['passed']) and len(checked['checks']) == 4
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
old = base / '20261116-scoped-history-checkpoint'
old_pins = json.loads(gzip.decompress((old / 'source-pins.json.gz').read_bytes()))
for name, digest in old_pins.items():
    assert sha(root / name) == digest, name

owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit = root / 'lean/MicroCFTA/Audit.lean'
prefix_name = 'SourcePruningEnumerationPrefixHeldHistoryAtOriginalBudget'
prefix_packet = base / '20261116-current-real-prefix-held-fragment-history-compose-repair'
prefix = prefix_packet / (prefix_name + '.lean')
assert sha(prefix) == '5803fed477359f4129cded2294e58b0792c5081a3d08ff39184b0bee961ddb5f'
prefix_target = root / 'lean/MicroCFTA' / prefix.name
assert not prefix_target.exists()
owner_before = owner.read_bytes()
audit_before = audit.read_bytes()
parts = [
    ('20261116-current-real-opaque-terminal-held-history-draft', 'cfcbed9f03d9abbbbd9487498a548eca2d77c272918dce6d263415e9773d7099'),
    ('20261116-current-real-captured-row-held-history-full-context-repair', '6f7e530d6a54603df03cdbc5f540ff612ec91d7cdfbf5e0ad1e9734eb9489f5d'),
    ('20261116-current-real-prepared-scan-held-history-prefix-name-repair', '1255f5f46897faa333d4ca2d40c133c7e800eb74037c6ead9768569254e24d7c'),
]
appendices = []
probes = (base / '20261116-scoped-history-publication/ResourceProbesWithScopedHistory165.lean.txt').read_bytes()
for folder, digest in parts:
    packet = base / folder
    assert sha(packet / 'APPEND.lean.txt') == digest
    appendices.append((packet / 'APPEND.lean.txt').read_bytes())
    probes += b'\n' + (packet / 'PROBES.lean.txt').read_bytes()
assert probes.count(b'#print axioms ') == 169
runtime = base / '20261116-prefix-opaque-row-component-publication'
runtime.mkdir()
(runtime / 'OWNER-BEFORE.lean.txt').write_bytes(owner_before)
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(audit_before)
new_import = ('import MicroCFTA.' + prefix_name + '\n').encode()
new_owner = new_import + owner_before + b'\nsection\nset_option maxHeartbeats 2000000\n' + b'\n'.join(appendices) + b'\nend\n'
new_audit = new_import + audit_before + b'\n' + (prefix_packet / 'PROBES.lean.txt').read_bytes()
prefix_target.write_bytes(prefix.read_bytes())
owner.write_bytes(new_owner)
audit.write_bytes(new_audit)
assert owner.read_bytes().split(b'\n', 1)[1].startswith(owner_before)
assert audit.read_bytes().split(b'\n', 1)[1].startswith(audit_before)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6172
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5172

objects = Path(tempfile.mkdtemp(prefix='mcfta-prefix-opaque-row-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'ResourceProbes169.lean.txt').write_bytes(probes)
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
independent.write_bytes(new_import + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + (prefix_packet / 'PROBES.lean.txt').read_bytes())
assert independent.read_bytes().count(b'#print axioms ') == 113
template = (private / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [
    ('public-build', 'exec lake build', 0),
    ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 169),
    ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 113),
    ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
    ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 518),
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
          'direct_audit_imports': 5172, 'individual_reports': 518, 'independent_reports': 113,
          'owner_resource_probes': 169, 'original_resource_probes': 136, 'total_private_resource_probes': 33,
          'audited_theorems': int(match.group(1)), 'new_public_prefix_history': True,
          'opaque_terminal_history_component': True, 'captured_row_history_component': True,
          'prepared_scan_history_component': True, 'outer_depth_history_proved': False,
          'joint_finite_completion_proved': False, 'haskell_changed': False, 'limits': limits,
          'at': datetime.datetime.now().astimezone().isoformat()}
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [source, runtime / 'ResourceProbes169.lean.txt', strict, independent, runtime / 'check.py', Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'resource_reports': 169, 'independent_reports': 113, 'audit_reports': 518}))
