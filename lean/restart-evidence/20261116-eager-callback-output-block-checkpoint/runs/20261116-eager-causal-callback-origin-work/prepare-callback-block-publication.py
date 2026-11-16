from pathlib import Path
import ast
import hashlib
import json
import tempfile

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
previous = base / '20261116-immediate-historical-suffix-kept-publication'
runtime = base / '20261116-real-eager-callback-output-block-publication'
sha = lambda data: hashlib.sha256(data).hexdigest()
specs = [
    ('SourcePruningEnumerationRealEagerCapturedOutputOrigin', '20261116-real-eager-row-origin-definitional-proof-repair', '0a2d4a6e138893a753bccc17b371d90e9f75d836e61e8faf96a17601f6708427', '20261116-row-and-scan-block-proof-repair-check'),
    ('SourcePruningEnumerationSharedScanOutputBlocks', '20261116-indexed-scan-output-block-match-reduction-repair', 'f1bb8046246162d47574738b2d6f0fade5eb717eec77c0031553016aa9abe1f3', '20261116-row-and-scan-block-proof-repair-check'),
    ('SourcePruningEnumerationSharedCallbackOutputBlocks', '20261116-generic-callback-output-blocks-proof-repair', 'fbc5674a8698338b6a29d5769f6540d7a4227287662b7ec7753cf6ecede98391', '20261116-generic-callback-output-blocks-proof-repair-check'),
    ('SourcePruningEnumerationSharedEagerOutputBlocks', '20261116-actual-eager-callback-output-blocks-explicit-parameters-draft', '01f6758d8ec9578e4ee139e72e2b594f20980a7ec9dfb24dc6ba99166ba8b553', '20261116-actual-eager-callback-output-blocks-check'),
    ('SourcePruningEnumerationRealEagerCapturedCallbackOrigin', '20261116-real-eager-captured-callback-restart-origin-stopped-repair', 'c690bb0e1c857c8a59319ac37798469f2a79b27f3561e5e73e9be5d04138d4e2', '20261116-real-eager-captured-callback-restart-repair-check'),
]
for check_name in sorted({entry[3] for entry in specs}):
    check = base / check_name
    result = json.loads((check / 'checked.json').read_text())
    assert all(result['passed'])
    for name, digest in json.loads((check / 'source-pins.json').read_text()).items():
        assert sha((root / name).read_bytes()) == digest, name
old_sources = {name: digest for name, digest in json.loads((previous / 'source-pins.json').read_text()).items()
               if name.startswith('lean/MicroCFTA/')}
assert len(old_sources) == 6185
for name, digest in old_sources.items():
    assert sha((root / name).read_bytes()) == digest, name
runtime.mkdir()
audit = root / 'lean/MicroCFTA/Audit.lean'
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
(runtime / 'AUDIT-BEFORE.lean.txt').write_bytes(audit.read_bytes())
(runtime / 'OWNER-UNCHANGED.lean.txt').write_bytes(owner.read_bytes())
note = b'''/- Note [Callback output blocks]
-------------------------------
Each callback can contribute a list of outputs.
OutputBlock keeps the whole list and one output index.
The list equality preserves order and duplicate occurrences.
The eager theorem derives this property by ordinary-height induction.
This property does not record a child invocation path.
An indexed invocation receipt is still needed to attach removed constraints.
-/

'''
reference = b'''/- See Note [Callback output blocks] in
MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks. -/
'''
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
    if name == 'SourcePruningEnumerationSharedCallbackOutputBlocks':
        anchor = b'/-- A callback contributes its whole output block at the original indexed occurrence. -/'
        annotation = note
    elif name == 'SourcePruningEnumerationSharedEagerOutputBlocks':
        anchor = b'theorem eager_child_callback_blocks\n'
        annotation = reference
    elif name == 'SourcePruningEnumerationRealEagerCapturedCallbackOrigin':
        anchor = b'theorem real_eager_captured_output_callback_restart_origin\n'
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
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6190
assert sum(line.startswith('import ') for line in audit.read_text().splitlines()) == 5190
assert audit.read_bytes().count(b'#print axioms ') == 551
objects = Path(tempfile.mkdtemp(prefix='mcfta-real-eager-callback-block-publication-'))
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
    command[command.index('-o') + 1] = str(objects / ('Owner.olean' if i == 0 else Path(command[-1]).stem + '.olean'))
    if i == 0:
        command[command.index('-R') + 1] = str(source.parent.parent)
        command[-1] = str(source)
for name, _, _, _ in specs:
    commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o', str(objects / (name + '.olean')), str(root / 'lean/MicroCFTA' / (name + '.lean'))])
commands.append(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '-o', str(objects / 'NewComponentProbes.olean'), str(runtime / 'NewComponentProbes.lean')])
strict = runtime / 'strict-modules.py'
strict.write_text('import subprocess\ncommands = ' + repr(commands) + '\nfor command in commands:\n    subprocess.run(command, check=True)\n')
independent = runtime / 'IndependentProbes.lean'
independent.write_bytes(imports + (previous / 'IndependentProbes.lean').read_bytes() + b'\n' + public_probes)
assert independent.read_bytes().count(b'#print axioms ') == 146
template = (base / specs[-1][3] / 'check.py').read_text()
driver = template[:template.index('\njobs =')]
jobs = [('public-build', 'exec lake build', 0),
        ('strict-resource-and-component-modules', 'exec python3 ' + str(strict), 218),
        ('independent-imports', 'exec lake env lean -j1 -DwarningAsError=true ' + str(independent), 146),
        ('audit-build', 'exec lake build MicroCFTA.Audit', 0),
        ('audit-strict', 'exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean', 551)]
driver += '\njobs = ' + repr(jobs) + '''
for name, command, count in jobs:
    run(name, command, count)
assert len(checks) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx']
           and (not job[2] or c['total_axiom_reports'] == job[2]) for c, job in zip(checks, jobs))
match = re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.', (runtime / 'audit-strict.txt').read_text())
assert match
report = {'checks': checks, 'source_pins_unchanged': True, 'source_files': 6190, 'direct_audit_imports': 5190,
          'individual_reports': 551, 'independent_reports': 146, 'resource_and_component_probes': 218,
          'owner_resource_probes': 208, 'original_resource_probes': 136, 'new_component_probes': 10,
          'audited_theorems': int(match.group(1)), 'new_modules': 5, 'new_public_theorems': 10,
          'actual_indexed_real_eager_row_origin_proved': True, 'whole_indexed_scan_output_block_proved': True,
          'genuine_actual_eager_height_callback_block_induction_proved': True,
          'exact_real_captured_callback_restart_output_block_proved': True,
          'indexed_executed_child_invocation_trace_proved': False, 'whole_worker_all_raw_aliases_proved': False,
          'every_causal_historical_event_attached_proved': False, 'joint_finite_completion_proved': False,
          'haskell_changed': False, 'limits': limits, 'at': datetime.datetime.now().astimezone().isoformat()}
(runtime / 'checked.json').write_text(json.dumps(report, indent=2) + '\\n')
print(json.dumps(report), flush=True)
'''
(runtime / 'check.py').write_text(driver)
files = list((root / 'lean/MicroCFTA').glob('*.lean'))
files += [root / n for n in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']]
files += [p for p in runtime.iterdir() if p.is_file()] + [source, Path(__file__)]
(runtime / 'source-pins.json').write_text(json.dumps({str(p.relative_to(root)): sha(p.read_bytes()) for p in files}, indent=2) + '\n')
print(json.dumps({'run': str(runtime), 'objects': str(objects), 'gates': 5, 'resource_and_component_probes': 218, 'independent_reports': 146, 'audit_reports': 551}))
