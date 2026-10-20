from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-native-original-union-descent'

def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')

module = 'SourceCurrentNativeOriginalUnionDescent'
assert json.loads((HERE / 'new-modules.json').read_text()) == [module]
proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
assert proof == '0b533a71852046e391dbed6e1c5761189465fa90'
(HERE / 'proof-commit.txt').write_text(proof + '\n')
write('selected-strict.json', {module: 'module-strict-1'})
write('selected-canonical.json', {module: 'module-canonical-1'})
write('selected-canonical-warnings.json', {module: re.findall(
    r'^warning:.*$', (HERE / 'module-canonical-1.log').read_text(), re.M)})
write('selected-groups.json', [
    dict(name='union-descent/union-descent-public-1', pairs=2, kind='new-public', full_proof=True),
    dict(name='union-fixture/union-descent-kernels-public-1', pairs=1, kind='constructed', full_proof=True),
])
write('selected-constructed-strict.json', {'fixture-strict-1': 'union-fixture/union-descent-kernels.lean'})
log = (HERE / 'root-full-audit-1.log').read_text()
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)', log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', log)[-1])
assert (jobs, dependencies) == (3536, 74283)
write('selected-audit.json', dict(name='root-full-audit-1', jobs=jobs, dependency_checks=dependencies,
                                root_observed_handle=45836, root_observed_terminal_exit=0))
write('expected-counts.json', dict(modules=1, pairs={'new-public': 2, 'constructed': 1, 'private-claim': 0},
                                 constructed_strict=1, audit_jobs=jobs, audit_dependency_checks=dependencies))
heads = ['MicroCFTA.' + module + '.' + name for name in re.findall(
    r'^(?:theorem|def|structure|inductive) ([A-Za-z0-9_.]+)',
    (ROOT / 'lean/MicroCFTA' / (module + '.lean')).read_text(), re.M)]
assert heads == ['MicroCFTA.' + module + '.' + name for name in ['UnionDescent', 'of_observed']]
write('public-heads.json', heads)
write('component-verifiers.json', [
    dict(path='union-descent/union-descent-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='union-fixture/union-descent-kernels-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='verify-reviews.py', arguments=[]),
    dict(path='next-publication-plan/plan-verify.py', arguments=['--live', '--root', str(ROOT)]),
])
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
write('attempt-accounting.json', dict(
    capped_commands=len(unique), failed_commands=sum(json.loads(key)['exit_code'] != 0 for key in unique),
    commands=[dict(receipts=paths, exit_code=json.loads(key)['exit_code']) for key, paths in unique.items()],
    receipt_copies_add_commands=False, selected_constructed_examples=1,
    constructed_family='The same box[nested,outer] warm source family; this version forces its returned binder arm.'))
fixture = json.loads((HERE / 'fixture-strict-1.json').read_text())
assert fixture['exit_code'] == 0 and not (HERE / 'fixture-strict-1.log').read_bytes()
write('selection-status.json', dict(
    finalized=True, public_pairs=2, constructed_pairs=1, root_fixture_observed_handle=int(sys.argv[1]),
    root_fixture_observed_terminal_exit=0, root_fixture_sha256=fixture['sha256'],
    root_module_observed_strict_handle=12709, root_module_observed_canonical_handle=29296,
    root_final_audit_observed_handle=45836, root_final_audit_observed_terminal_exit=0))
write('goal-turn.json', dict(
    classification='progress', goal_status='active', prior_checkpoint='533db5d24c143837cc5bcf63a9d3522491d52178',
    proof_commit=proof,
    new_route='Same actual SourceRow jointly supplies terminal call and original-union descent. One fixed original Observed event/raw supports all stored rows and actual unfold anchors. The warm source forces its returned nested-binder branch without selecting an independent terminal or assuming writer identity.',
    interface_limit='Pure source descent does not give intermediate call uniqueness, strict historical-writer order or a global native renewal rank.',
    remaining=['causal ordering of resumed historical writers', 'generated-capture original ancestry', 'residual Mu observations',
               'global renewal and active-owner exclusion', 'final owner retention',
               'outer completion and convergence', 'Haskell refinement'], counts_are_not_completion_measure=True))
write('current-documents.json', [
    'NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
    'lean/notes-current-system-claim.md', 'lean/notes-current-native-original-union-descent.md',
    'lean/MicroCFTA/Audit.lean'])
print(json.dumps(dict(public_heads=len(heads), capped_commands=len(unique),
                      failed_commands=sum(json.loads(key)['exit_code'] != 0 for key in unique))))
