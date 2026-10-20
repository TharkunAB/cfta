from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-native-original-observed-resume'

def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')

module = 'SourceCurrentNativeOriginalObservedResume'
names = json.loads((HERE / 'new-modules.json').read_text())
assert names == [module]
proof = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
assert proof == '9cff855cfe987fbe73ce0c00af40cb38be765fce'
(HERE / 'proof-commit.txt').write_text(proof + '\n')
write('selected-strict.json', {module: 'module-strict-1'})
write('selected-canonical.json', {module: 'module-canonical-1'})
write('selected-canonical-warnings.json', {module: re.findall(
    r'^warning:.*$', (HERE / 'module-canonical-1.log').read_text(), re.M)})
write('selected-groups.json', [
    dict(name='observed-resume/observed-resume-public-1', pairs=2, kind='new-public', full_proof=True),
    dict(name='observed-fixture/observed-resume-kernels-public-1', pairs=1, kind='constructed', full_proof=True),
])
write('selected-constructed-strict.json', {'fixture-strict-1': 'observed-fixture/observed-resume-kernels.lean'})
audit_log = (HERE / 'root-full-audit-1.log').read_text()
jobs = int(re.findall(r'Build completed successfully \((\d+) jobs\)', audit_log)[-1])
dependencies = int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit_log)[-1])
assert (jobs, dependencies) == (3535, 74276)
write('selected-audit.json', dict(name='root-full-audit-1', jobs=jobs, dependency_checks=dependencies,
                                root_observed_handle=55982, root_observed_terminal_exit=0))
write('expected-counts.json', dict(modules=1, pairs={'new-public': 2, 'constructed': 1, 'private-claim': 0},
                                 constructed_strict=1, audit_jobs=jobs, audit_dependency_checks=dependencies))
heads = ['MicroCFTA.' + module + '.' + name for name in re.findall(
    r'^(?:theorem|def|structure|inductive) ([A-Za-z0-9_.]+)',
    (ROOT / 'lean/MicroCFTA' / (module + '.lean')).read_text(), re.M)]
assert heads == ['MicroCFTA.' + module + '.' + name for name in ['SyntaxBound', 'of_observed']]
write('public-heads.json', heads)
write('component-verifiers.json', [
    dict(path='observed-resume/observed-resume-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='observed-fixture/observed-resume-kernels-verify.py', arguments=['--live', '--root', str(ROOT)]),
    dict(path='verify-reviews.py', arguments=[]),
    dict(path='next-union-descent-plan/plan-verify.py', arguments=['--live', '--root', str(ROOT)]),
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
    constructed_family='The same box[nested,outer] warm source family as the preceding checkpoint.'))
fixture = json.loads((HERE / 'fixture-strict-1.json').read_text())
assert fixture['exit_code'] == 0 and not (HERE / 'fixture-strict-1.log').read_bytes()
write('selection-status.json', dict(
    finalized=True, public_pairs=2, constructed_pairs=1, root_fixture_observed_handle=34512,
    root_fixture_observed_terminal_exit=0, root_fixture_sha256=fixture['sha256'],
    root_module_observed_strict_handle=72921, root_module_observed_canonical_handle=58848,
    root_final_audit_observed_handle=55982, root_final_audit_observed_terminal_exit=0))
write('goal-turn.json', dict(
    classification='progress', goal_status='active', prior_checkpoint='296d6f99c9f760f92b5fae71f7f31548e133c634',
    proof_commit=proof,
    new_route='One observed original writer retains the same actual terminal tuple and adds actual indexed node calls or exact selected binder-payload resumption for every stored row and actual unfold anchor.',
    interface_limit='Global Reached, non-strict syntax bound and forward suffix do not expose union-only source descent. The concrete result retains its node-or-binder disjunction.',
    remaining=['same-terminal union descent', 'generated-capture original ancestry', 'residual Mu observations',
               'global renewal and active-owner exclusion', 'final owner retention',
               'outer completion and convergence', 'Haskell refinement'], counts_are_not_completion_measure=True))
write('current-documents.json', [
    'NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
    'lean/notes-current-system-claim.md', 'lean/notes-current-native-original-observed-resume.md',
    'lean/MicroCFTA/Audit.lean'])
print(json.dumps(dict(public_heads=len(heads), capped_commands=len(unique),
                      failed_commands=sum(json.loads(key)['exit_code'] != 0 for key in unique))))
