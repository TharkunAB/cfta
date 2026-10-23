exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
assert git('branch', '--show-current').strip() == 'formalize'
assert git('rev-parse', 'HEAD').strip() == START
assert not git('diff', '--cached', '--name-only').strip()
assert load(HERE / 'root-source-history-review.json')['status'] == 'ACCEPTED_COMPLETE_SELECTED_SOURCE_AND_ACTUAL_HISTORY'
for mode, live in [('normal', False), ('live', True)]:
    report = load(HERE / ('proof-evidence-' + mode + '.json'))
    assert report['status'] == 'PASS' and report['live'] is live
    assert report['actual_jobs'] == 3 and report['selected_modules'] == 1
    assert report['public_theorems'] == 3 and report['failed_jobs'] == 0
    assert report['audit_dependencies'] == 75553 and report['new_lean_lake_jobs'] == 0
selected = load(HERE / 'selected-sources.json')
assert len(selected) == 1
paths = sorted(selected) + ['lean/MicroCFTA/Audit.lean']
assert set(git('diff', '--name-only').splitlines()) == {'lean/MicroCFTA/Audit.lean'}
for path, pin in selected.items():
    assert sha(ROOT / path) == pin['sha256']
    assert (ROOT / path).read_bytes() == (HERE / (Path(path).stem + '.lean')).read_bytes()
subprocess.run(['git', 'diff', '--check', '--', *paths], cwd=ROOT, check=True)
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Prove node counter growth in stored execution'], cwd=ROOT, check=True)
proof = git('rev-parse', 'HEAD').strip()
assert git('rev-parse', proof + '^').strip() == START
assert set(git('diff-tree', '--no-commit-id', '--name-only', '-r', proof).splitlines()) == set(paths)
assert not (HERE / 'proof-commit.txt').exists()
(HERE / 'proof-commit.txt').write_text(proof + '\n')
print(json.dumps(dict(status='PASS', proof_commit=proof, proof_files=paths, goal_status='ACTIVE_INCOMPLETE')))
