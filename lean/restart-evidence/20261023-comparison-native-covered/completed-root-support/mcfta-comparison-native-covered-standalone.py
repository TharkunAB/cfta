import runpy
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))
assert not (HERE / 'proof-commit.txt').exists()
assert git('rev-parse', 'HEAD').strip() == START
for mode, extra in [('normal', []), ('live', ['--live'])]:
    result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-proofs.py'),
        '--root', str(ROOT), *extra], cwd='/', capture_output=True, text=True)
    for suffix, content in [('stdout', result.stdout), ('stderr', result.stderr)]:
        path = HERE / ('standalone-' + mode + '.' + suffix)
        assert not path.exists()
        path.write_text(content)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['live'] is bool(extra)
    assert report['actual_jobs'] == 3 and report['source_jobs'] == 2 and report['audit_jobs'] == 1
    assert report['failed_jobs'] == report['warned_source_exit_zero_jobs'] == report['rejected_public_type_jobs'] == 0
    assert report['root_metadata_jobs'] == 15 and report['failed_root_metadata_jobs'] == 3
    assert report['audit_build_jobs'] == 3645 and report['audit_dependencies'] == 75508
    save('proof-evidence-' + mode + '.json', report)
print(json.dumps(dict(status='PASS', modes=['normal', 'live'], cwd='/', before_proof_commit_and_documents=True)))
