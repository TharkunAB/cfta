import datetime
import re
import runpy
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

assert load(HERE / 'root-bound-tools-review.json')['status'] == 'ROOT_BOUND_TOOL_REVIEW_CLEAR'
stem = 'completed-hit-readback-audit-1'
receipt = load(HERE / (stem + '.json'))
assert receipt['exit_code'] == 0 and receipt['command'][-2:] == ['build', 'MicroCFTA.Audit']
raw = HERE / (stem + '.log')
audit_text = raw.read_text()
assert 'Build completed successfully (3644 jobs).' in audit_text
assert 'Checked axiom dependencies of 75507 MicroCFTA theorems.' in audit_text
assert sha(raw) == '29318583ac1dc0be2b57a786bd01643bee63c16c849f5bc9f199cf5bcd513376'
assert not re.search(r'\berror(?:\([^)]*\))?:', audit_text)
assert len(re.findall(r'^warning:', audit_text, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit_text
assert (HERE / 'completed-hit-readback-strict-1.log').read_bytes() == b''
save('root-audit-review.json', dict(status='PASS', observed_at=datetime.datetime.now().astimezone().isoformat(),
    actual_lean_lake_jobs=3, source_jobs=2, audit_jobs=1, failed_jobs=0,
    warned_source_exit_zero_jobs=0, rejected_public_type_jobs=0,
    audit_build_jobs=3644, audit_dependencies=75507, audit_log_sha256=sha(raw),
    old_replay_warning_only=True, new_source_clean=True, whole_goal_complete=False))
for label, flags in [('normal', []), ('live', ['--live'])]:
    result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-proofs.py'), '--root', str(ROOT), *flags],
        cwd='/', capture_output=True, text=True)
    for suffix, value in [('stdout', result.stdout), ('stderr', result.stderr)]:
        path = HERE / ('proof-evidence-' + label + '.' + suffix)
        assert not path.exists()
        path.write_text(value)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['live'] is (label == 'live')
    assert report['actual_jobs'] == 3 and report['source_jobs'] == 2 and report['audit_jobs'] == 1
    assert report['failed_jobs'] == report['warned_source_exit_zero_jobs'] == report['rejected_public_type_jobs'] == 0
    assert report['audit_build_jobs'] == 3644 and report['audit_dependencies'] == 75507
    path = HERE / ('proof-evidence-' + label + '.json')
    assert not path.exists()
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(mode=label, report=report)))
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Aggregate Audit and saved proofs passed\n\nAll three actual Lean/Lake commands pass. Strict1 has an empty log.\nThe sole FULL1 and Audit1 pass. Audit has3644 jobs and75507 dependencies.\nOnly the old unused inputs warning is replayed. New source is clean.\nBoth147-line proposal drafts and their exact precompiler cleanup remain.\nNo compiler repair was needed. Normal and live saved proofs pass from cwd /.\nBoth saved modes passed before any document write.\nProof commit, documents, closing preservation, seal and push remain pending.\nThe whole goal remains ACTIVE.\n')
