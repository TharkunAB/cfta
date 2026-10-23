exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
import datetime
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert proof == 'ff8e7ad52c126559ba3c7028f0e7eb4130bc4f8f'
assert git('rev-parse', 'HEAD').strip() == proof
verification = load(HERE / 'verification.json')
assert verification['status'] == 'PASS' and verification['baseline_files'] == 110256
assert verification['actual_jobs'] == 3 and verification['failed_jobs'] == 0
assert load(HERE / 'proof-evidence-normal.json')['status'] == 'PASS'
assert load(HERE / 'proof-evidence-live.json')['status'] == 'PASS'
addition = '''
## Actual proof and local checkpoint checks

The 100-line source passed strict1 with a literal empty log and sole FULL1.
Root and an independent reviewer read the complete 832-line checked TYPE.
Printed TYPE identity and complete BODY retention were checked programmatically.
The sole aggregate Audit passed 3649 jobs and 75526 theorem dependencies.
All three Lean/Lake jobs passed. One mathematical variant remains unchanged.
The saved verifier passed normal and live modes from cwd / before the proof commit.
The proof commit is ff8e7ad52c126559ba3c7028f0e7eb4130bc4f8f.
All nine additive document inverses and FINDINGS repair ordering pass.
The local checkpoint check preserves 110256 baseline files and modes,
3647 older non-Audit Lean sources, 298 Haskell and 207 package files.
It checks 314 historical frozen registries, 1410 entries and five archived overrides.
The source-only reconstruction plan remains separate from the checked H30 theorem.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
Support collection, the mandatory seal rerun, local publication and push remain future work.
'''
path = HERE / 'current-progress.md'
assert '## Actual proof and local checkpoint checks' not in path.read_text()
with path.open('a') as stream:
    stream.write(addition)
save('root-actual-local-progress.json', dict(status='ACTUAL_PROOF_AND_PRESEAL_CHECKPOINT_PASS',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), proof_commit=proof,
    verification_sha256=sha(HERE / 'verification.json'), progress_sha256=sha(path),
    whole_goal_complete=False, seal_or_push_success_claimed=False))
print('Recorded actual proof and pre-seal checkpoint outcomes without future publication claims.')
