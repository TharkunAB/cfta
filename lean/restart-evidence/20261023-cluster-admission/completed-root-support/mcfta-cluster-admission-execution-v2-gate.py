exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-cluster-admission-execution-source-v2')
review = Path('/tmp/mcfta-cluster-admission-execution-body-v2-audit')
checked_package(owner, 'a35dfe348366e8e7f7c83d118353af65adaef13f41df659416ba89d3f782ba56', 'd87dcec586d4ac239edfc571c9595f22a8c0eaa5e58365dc6db5b919ac1941b4')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
source = owner / (NAME + '.lean')
assert sha(source) == 'ee67ecabee46dd20e570eba723a816849c6d28f31a9e14d794eb4026a56092bb'
old = (HERE / 'execution-source-v1' / (NAME + '.lean')).read_text()
new = source.read_text()
assert new == old.replace('[execute,', '[SourceCurrentOriginalRowClusterScan.execute,').replace('[Nat.succ_add, execute,', '[Nat.succ_add, SourceCurrentOriginalRowClusterScan.execute,')
assert len(new.splitlines()) == 64
assert load(HERE / 'execution-strict1.json')['exit_code'] == 1
assert sha(HERE / 'execution-strict1.source.lean') == '2bbaf50ee3540963968e37202e0fc4a331e5d4063f717feec579966ced81920b'
assert (HERE / 'execution-strict1.log').stat().st_size > 0
for fragment in (HERE / 'execution-declaration-plan').glob('*.lean.txt'):
    expected = fragment.read_text().rstrip()
    assert expected in new
archive(owner, 'execution-source-v2')
archive(review, 'execution-body-v2-audit')
save('root-execution-v2-body-gate.json', {
    'status': 'ACCEPTED_SOURCE_BODY_FOR_STRICT', 'source_sha256': sha(source), 'lines': 64,
    'root_complete_source_and_diff_read': True,
    'unchanged_exact_declarations_and_IH': True,
    'independent_body_review_sha256': sha(review / 'review.json'),
    'strict_compiler_activation_authorized': True, 'FULL_activation_authorized': False,
    'failed_variant_and_raw_log_retained': True,
    'repair': 'Use the fully qualified execute declaration in six simp lists.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: exact six-reference simplifier repair accepted; original failure retained')
