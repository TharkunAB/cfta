import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read(name):
    return json.loads((HERE / name).read_text())


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


module = 'SourceCurrentNativeGeneratedRowCaptureBackedge'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert proof == '57fe78e0e5f0d127f8ee350a6a485b8e2636e594'
archived = read('archived-components.json')
if not any(item['path'] == 'prefix-helper' for item in archived):
    archived.append(dict(path='prefix-helper', manifest='helper-manifest.json',
        manifest_sha256='3f25dad8ac9cd3db349f9cff8076a045c19bfe89c88263dfbf10684c98ec8e17'))
write('archived-components.json', archived)
write('selected-strict.json', {module: 'root-backedge-strict-2'})
write('selected-canonical.json', {module: 'root-backedge-canonical-1'})
write('selected-canonical-warnings.json', {
    module: re.findall(r'^warning:.*$', (HERE / 'root-backedge-canonical-1.log').read_text(), re.M)})
fixture = read('capture-fixture/backedge-kernels-selection.json')
assert fixture['finalized']
fixture_group = fixture['groups'][0]
assert len(fixture['groups']) == 1 and fixture_group['pairs'] == 1 and fixture_group['full_proof']
write('selected-groups.json', [
    dict(name='backedge-module/generated-row-backedge-public-3', pairs=1,
         kind='new-public', full_proof=True),
    dict(name='capture-fixture/' + fixture_group['name'], pairs=1,
         kind='constructed', full_proof=True)])
write('selected-constructed-strict.json', {
    'root-backedge-fixture-strict-1': 'capture-fixture/' + fixture['source']})
log = (HERE / 'root-backedge-audit-1.log').read_text()
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', log)[-1])
assert (jobs, dependencies) == (3541, 74341)
write('selected-audit.json', dict(name='root-backedge-audit-1', jobs=jobs,
      dependency_checks=dependencies, root_observed_handle=68968, root_observed_terminal_exit=0))
write('expected-counts.json', dict(modules=1,
      pairs={'new-public': 1, 'constructed': 1, 'private-claim': 0}, constructed_strict=1,
      audit_jobs=jobs, audit_dependency_checks=dependencies))
heads = ['MicroCFTA.' + module + '.' + name for name in re.findall(
    r'^(?:theorem|def|structure|inductive) ([A-Za-z0-9_.]+)',
    (ROOT / 'lean/MicroCFTA' / (module + '.lean')).read_text(), re.M)]
assert heads == ['MicroCFTA.' + module + '.generated_row_capture_backedge']
write('public-heads.json', heads)
write('component-verifiers.json', [
    dict(path='backedge-module/generated-row-backedge-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='backedge-core/generated-backedge-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='source-review/math-review-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='prefix-helper/helper-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='capture-fixture/backedge-kernels-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='fixture-review/fixture-review-verify.py', arguments=[
        '--live', '--root', str(ROOT), '--fixture', str(HERE / 'capture-fixture')]),
    dict(path='verify-compressed.py', arguments=[])])
unique = {}
diagnostics = {}
for path in HERE.rglob('*.json'):
    try:
        data = json.loads(path.read_text())
    except ValueError:
        diagnostics[str(path.relative_to(HERE))] = hashlib.sha256(path.read_bytes()).hexdigest()
        continue
    if (isinstance(data, dict) and isinstance(data.get('command'), list)
            and isinstance(data.get('exit_code'), int) and 'wrapper' in data
            and Path(data['command'][0]).name in ['lean', 'lake']):
        unique.setdefault(json.dumps(data, sort_keys=True), []).append(str(path.relative_to(HERE)))
write('non-json-evidence.json', diagnostics)
write('attempt-accounting.json', dict(capped_commands=len(unique),
      failed_commands=sum(json.loads(key)['exit_code'] != 0 for key in unique),
      commands=[dict(receipts=paths, exit_code=json.loads(key)['exit_code'])
                for key, paths in unique.items()],
      receipt_copies_add_commands=False, rejected_zero_exit_printers=1,
      selected_constructed_examples=1,
      constructed_family='One validated V2 union-body source example from three attempted variants. '
                         'An actual 60-step native prefix creates a new used outer full Mu. '
                         'The same returned variable2/pool1 capture retains its initial full cell '
                         'and same-row original node RowCall. No actual unfold is executed.',
      auxiliary_helper_readbacks=0))
strict = read('root-backedge-fixture-strict-1.json')
assert strict['exit_code'] == 0 and not (HERE / 'root-backedge-fixture-strict-1.log').read_bytes()
write('selection-status.json', dict(finalized=True, public_pairs=1, constructed_pairs=1,
      root_fixture_observed_handle=int(sys.argv[1]), root_fixture_observed_terminal_exit=0,
      root_fixture_sha256=strict['sha256'], root_module_observed_strict_handle=92144,
      root_module_observed_canonical_handle=81454, root_final_audit_observed_handle=68968,
      root_final_audit_observed_terminal_exit=0))
write('goal-turn.json', dict(classification='progress', goal_status='active',
      prior_checkpoint='0dab9a59db6800007041371af7adea8c4898274d', proof_commit=proof,
      new_route='One actual generated Observed fixes its event and raw callback before all rows. '
                'The same full-Mu capture retains an exact leaves slot, residency and distinct target key. '
                'Its same complete row has original indexed node production or an actual earlier native producer.',
      interface_limit='Full-Mu capture ancestry is proved. Node, binder and non-Mu capture cases remain explicit. '
                      'No global native termination or implementation refinement follows.',
      remaining=['generated node and non-Mu capture ancestry', 'warm binder reuse', 'self replacement',
                 'residual Mu observations', 'global renewal and active-owner exclusion',
                 'final owner retention', 'outer completion and convergence', 'Haskell refinement'],
      counts_are_not_completion_measure=True))
write('current-documents.json', ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md',
      'lean/README.md', 'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
      'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md',
      'lean/notes-current-native-generated-row-capture-backedge.md', 'lean/MicroCFTA/Audit.lean'])
print(json.dumps(dict(status='PASS', public_heads=len(heads), capped_commands=len(unique),
      failed_commands=sum(json.loads(key)['exit_code'] != 0 for key in unique))))
