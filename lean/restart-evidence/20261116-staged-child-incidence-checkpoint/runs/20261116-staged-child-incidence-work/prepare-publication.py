from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
previous = base / '20261116-indexed-causal-invocation-publication'
runtime = base / '20261116-staged-child-incidence-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
prior = json.loads((previous / 'checked.json').read_text())
specs = json.loads((work / 'publication-selection.json').read_text())
assert len(specs) == 4
for name, folder, digest, check_name in specs:
    check = base / check_name
    result = json.loads((check / 'checked.json').read_text())
    assert all(result['passed'])
    for path, pin in json.loads((check / 'source-pins.json').read_text()).items():
        assert sha((root / path).read_bytes()) == pin, path
    assert sha((base / folder / (name + '.lean')).read_bytes()) == digest
old_sources = {name: digest for name, digest in json.loads((previous / 'source-pins.json').read_text()).items()
               if name.startswith('lean/MicroCFTA/')}
assert len(old_sources) == prior['source_files'] == 6195
for name, digest in old_sources.items():
    assert sha((root / name).read_bytes()) == digest, name
runtime.mkdir()
audit = root / 'lean/MicroCFTA/Audit.lean'
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(audit.read_bytes())
(runtime / 'OWNER-UNCHANGED.lean.txt').write_bytes(owner.read_bytes())
public_probes = b''
transformations = []
for name, folder, digest, check_name in specs:
    raw = (base / folder / (name + '.lean')).read_bytes()
    assert sha(raw) == digest and b'set_option maxHeartbeats' not in raw
    source = root / 'lean/MicroCFTA' / (name + '.lean')
    if source.exists():
        assert source.read_bytes() == raw, source
    source.write_bytes(raw)
    public_probes += b'\n' + (base / folder / 'PROBES.lean.txt').read_bytes()
    transformations.append({'module': name, 'packet': folder, 'checked_raw_sha256': digest,
                            'public_sha256': digest, 'annotation_only': False, 'annotation': '',
                            'statements_definitions_and_proofs_unchanged': True})
new_reports = public_probes.count(b'#print axioms ')
assert new_reports == 9
imports = b''.join(('import MicroCFTA.' + row[0] + '\n').encode() for row in specs)
old_audit = audit.read_bytes()
audit.write_bytes(imports + old_audit + b'\n' + public_probes)
assert audit.read_bytes().split(b'\n', len(specs))[len(specs)].startswith(old_audit)
source_count = prior['source_files'] + len(specs)
audit_count = prior['direct_audit_imports'] + len(specs)
audit_reports = prior['individual_reports'] + new_reports
resource_reports = prior['resource_and_component_probes'] + new_reports
independent_reports = prior['independent_reports'] + new_reports
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == source_count
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == audit_count
assert audit.read_bytes().count(b'#print axioms ') == audit_reports
objects = Path(tempfile.mkdtemp(prefix='mcfta-staged-child-incidence-publication-'))
(runtime / 'objects.json').write_text(json.dumps({'path': str(objects)}, indent=2) + '\n')
(runtime / 'selection.json').write_text(json.dumps(specs, indent=2) + '\n')
(runtime / 'source-transformations.json').write_text(json.dumps(transformations, indent=2) + '\n')
(runtime / 'NewComponentProbes.lean').write_bytes(imports + public_probes)
(runtime / 'ResourceProbes208.lean.txt').write_bytes((previous / 'ResourceProbes208.lean.txt').read_bytes())
source = runtime / 'source/MicroCFTA' / owner.name
source.parent.mkdir(parents=True)
source.write_bytes(owner.read_bytes() + b'\n' + (runtime / 'ResourceProbes208.lean.txt').read_bytes())
tree = ast.parse((previous / 'strict-modules.py').read_text())
commands = ast.literal_eval(next(x.value for x in tree.body if isinstance(x, ast.Assign)))
for i, command in enumerate(commands):
    command[command.index('-o') + 1] = str(objects / (str(i).zfill(3) + '-' + Path(command[-1]).stem + '.olean'))
    if i == 0:
        command[command.index('-R') + 1] = str(source.parent.parent)
        command[-1] = str(source)
for name, _, _, _ in specs:
    commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o', str(objects / (name + '.olean')), str(root / 'lean/MicroCFTA' / (name + '.lean'))])
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o', str(objects / 'CurrentNewComponentProbes.olean'), str(runtime / 'NewComponentProbes.lean')])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(imports + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + public_probes)
assert independent.read_bytes().count(b'#print axioms ') == independent_reports
template = (base / specs[-1][3] / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [('public-build', 'exec lake build', 0),
        ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), resource_reports),
        ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), independent_reports),
        ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
        ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', audit_reports)]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'checks': checks, 'source_pins_unchanged': True,
          'audited_theorems': int(match.group(1)), 'owner_resource_probes': 208,
          'original_resource_probes': 136, 'new_relation_declaration_reports': 0,
          'local_primitive_all_raw_alias_growth_proved': True,
          'specified_staged_child_position_incidence_proved': True,
          'same_selected_preparation_indexed_child_bridge_proved': True,
          'actual_shared_child_all_raw_alias_growth_proved': True,
          'whole_worker_all_raw_aliases_proved': False,
          'every_causal_historical_event_attached_proved': False,
          'joint_finite_completion_proved': False, 'haskell_changed': False,
          'limits': limits, 'at': datetime.datetime.now().astimezone().isoformat()}
'''
driver += 'report.update(' + repr({'source_files': source_count, 'direct_audit_imports': audit_count,
    'individual_reports': audit_reports, 'independent_reports': independent_reports,
    'resource_and_component_probes': resource_reports, 'new_component_reports': new_reports,
    'new_theorem_reports': new_reports, 'new_modules': len(specs), 'new_public_theorems': new_reports}) + ')\n'
driver += "(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')\nprint(json.dumps(report), flush=True)\n"
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in runtime.iterdir() if p.is_file()] + [source, Path(__file__)]
files += [Path(command[-1]) for command in commands]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes()) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5,
                  'source_files': source_count, 'resource_and_component_probes': resource_reports,
                  'independent_reports': independent_reports, 'audit_reports': audit_reports}))
