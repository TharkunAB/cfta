exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import sys
mode = sys.argv[1]
assert mode in ('normal', 'live')
gate = load(HERE / 'root-proof-verifier-v2-review.json')
assert gate['status'] == 'ACCEPTED_WHOLE_REVIEWED_V2_FOR_STANDALONE_DUAL_MODE_EXECUTION'
assert sha(HERE / 'verify-proofs.py') == gate['verifier_sha256']
assert sha(HERE / 'bound-data.json') == gate['bound_data_sha256']
report_path = HERE / ('proof-evidence-' + mode + '.json')
assert not report_path.exists()
command = ['/usr/bin/python3', str(HERE / 'verify-proofs.py'), '--root', str(ROOT)]
if mode == 'live':
    command.append('--live')
result = subprocess.run(command, cwd='/', capture_output=True)
for label, data in [('stdout', result.stdout), ('stderr', result.stderr)]:
    path = HERE / ('standalone-proof-' + mode + '.' + label)
    assert not path.exists()
    path.write_bytes(data)
assert result.returncode == 0, result.stderr.decode()
report = json.loads(result.stdout)
assert report['status'] == 'PASS' and report['live'] is (mode == 'live')
assert report['actual_jobs'] == 12 and report['selected_modules'] == 3
assert report['public_theorems'] == 6 and report['failed_jobs'] == 3
assert report['new_lean_lake_jobs'] == 0
save(report_path.name, report)
print(json.dumps(report))
