from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
previous = base / '20261116-real-eager-callback-output-block-publication'
runtime = base / '20261116-indexed-causal-invocation-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
specs = [('SourcePruningEnumerationSharedInvocationTrace', '20261116-indexed-invocation-trace-abi-noted-probes', '2f20b9bd96108c88ceba71f6ee69cb07aeb2bf03fbd490fdb2ab0c36953c11f3', '20261116-indexed-invocation-trace-abi-check'), ('SourcePruningEnumerationSharedInvocationCombinators', '20261116-indexed-invocation-combinators-explicit-visitor-repair', 'ea15f23a521b281439dedfc7157e656b102ea9aee1c8a164595ab522f646b98e', '20261116-indexed-invocation-combinators-explicit-check'), ('SourcePruningEnumerationSharedChildInvocationOrigins', '20261116-actual-child-invocation-origins-draft', 'bc85d4a3ad520b605d1d8576b58f06e37ab8e3e2804f9e3ef3c4cb226d2fb59b', '20261116-actual-child-invocation-origins-check'), ('SourcePruningEnumerationRealEagerCapturedCausalCallbackOrigin', '20261116-real-eager-captured-causal-callback-invocation-draft', '6a23c72adbdad182b8a7cbe0121a7e08cb1dc480e748256b570b43a041af1446', '20261116-real-eager-captured-causal-invocation-check'), ('SourcePruningEnumerationSharedInvocationInversions', '20261116-indexed-invocation-inversions-bool-repair', '2f86c6e654d6662bfc89e9c365f4bf61220f5fe16d5d9b954f00bcaa2d4a88b7', '20261116-indexed-invocation-inversions-bool-verified-check')]
for check_name in sorted({entry[3] for entry in specs}):
    check = base / check_name
    result = json.loads((check / 'checked.json').read_text())
    assert all(result['passed'])
    for name, digest in json.loads((check / 'source-pins.json').read_text()).items():
        assert sha((root / name).read_bytes()) == digest, name
old_sources = {name: digest for name, digest in json.loads((previous / 'source-pins.json').read_text()).items()
               if name.startswith('lean/MicroCFTA/')}
assert len(old_sources) == 6190
for name, digest in old_sources.items():
    assert sha((root / name).read_bytes()) == digest, name
runtime.mkdir()
audit = root / 'lean/MicroCFTA/Audit.lean'
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(audit.read_bytes())
(runtime / 'OWNER-UNCHANGED.lean.txt').write_bytes(owner.read_bytes())
reference = b"/- See Note [Indexed invocation ancestry] in\nMicroCFTA.SourcePruningEnumerationSharedInvocationTrace. -/\n"
public_probes = b''
transformations = []
for name, folder, digest, check_name in specs:
    packet = base / folder
    raw = (packet / (name + '.lean')).read_bytes()
    assert sha(raw) == digest
    assert b'set_option maxHeartbeats' not in raw
    source = root / 'lean/MicroCFTA' / (name + '.lean')
    if source.exists():
        assert source.read_bytes() == raw, source
    annotation = b''
    anchors = {
        'SourcePruningEnumerationSharedInvocationCombinators': b'theorem children_invocation_origin\n',
        'SourcePruningEnumerationSharedChildInvocationOrigins': b'theorem shallow_invocation_at\n',
        'SourcePruningEnumerationSharedInvocationInversions': b'theorem selected_complete_invocation\n',
    }
    if name in anchors:
        anchor = anchors[name]
        annotation = reference
    annotated = raw
    if annotation:
        assert raw.count(anchor) == 1
        annotated = raw.replace(anchor, annotation + anchor)
        assert annotated.replace(annotation, b'', 1) == raw
    source.write_bytes(annotated)
    public_probes += b'\n' + (packet / 'PROBES.lean.txt').read_bytes()
    transformations.append({'module': name, 'packet': folder, 'checked_raw_sha256': digest,
                            'public_sha256': sha(annotated), 'annotation_only': bool(annotation),
                            'annotation': annotation.decode(), 'statements_definitions_and_proofs_unchanged': True})
assert public_probes.count(b'#print axioms ') == 10
imports = b''.join(('import MicroCFTA.' + name + '\n').encode() for name, _, _, _ in specs)
old_audit = audit.read_bytes()
audit.write_bytes(imports + old_audit + b'\n' + public_probes)
assert audit.read_bytes().split(b'\n', 5)[5].startswith(old_audit)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6195
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5195
assert audit.read_bytes().count(b'#print axioms ') == 561
objects = Path(tempfile.mkdtemp(prefix='mcfta-indexed-causal-invocation-publication-'))
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
    command[command.index('-o') + 1] = str(objects / ('000-Owner.olean' if i == 0 else str(i).zfill(3) + '-' + Path(command[-1]).stem + '.olean'))
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
assert independent.read_bytes().count(b'#print axioms ') == 156
template = (base / specs[-1][3] / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [('public-build', 'exec lake build', 0),
        ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 228),
        ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 156),
        ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
        ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 561)]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'checks': checks, 'source_pins_unchanged': True, 'source_files': 6195, 'direct_audit_imports': 5195,
          'individual_reports': 561, 'independent_reports': 156, 'resource_and_component_probes': 228,
          'owner_resource_probes': 208, 'original_resource_probes': 136, 'new_component_reports': 10,
          'new_relation_declaration_reports': 3, 'new_theorem_reports': 7,
          'audited_theorems': int(match.group(1)), 'new_modules': 5, 'new_public_theorems': 7,
          'concrete_indexed_invocation_relations_kernel_checked': True,
          'actual_eager_indexed_invocation_producer_proved': True,
          'strong_captured_invocation_same_original_witnesses_proved': True,
          'literal_prepare_and_terminal_dispatch_inversions_proved': True,
          'every_staged_child_position_incidence_proved': False, 'whole_worker_all_raw_aliases_proved': False,
          'every_causal_historical_event_attached_proved': False, 'joint_finite_completion_proved': False,
          'haskell_changed': False, 'limits': limits, 'at': datetime.datetime.now().astimezone().isoformat()}
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in runtime.iterdir() if p.is_file()] + [source, Path(__file__)]
files += [Path(command[-1]) for command in commands]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes()) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'resource_and_component_probes': 228, 'independent_reports': 156, 'audit_reports': 561}))
