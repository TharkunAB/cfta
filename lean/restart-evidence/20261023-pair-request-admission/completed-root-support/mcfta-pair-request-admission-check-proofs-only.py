import runpy
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

assert load(HERE / 'root-bound-tools-review.json')['status'] == 'ROOT_BOUND_TOOL_REVIEW_CLEAR'
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
    assert report['audit_build_jobs'] == 3642 and report['audit_dependencies'] == 75503
    path = HERE / ('proof-evidence-' + label + '.json')
    assert not path.exists()
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(mode=label, report=report)))
