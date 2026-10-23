exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import re
import sys
owner = Path('/tmp/mcfta-cluster-admission-execution-source-v1')
review = Path('/tmp/mcfta-cluster-admission-execution-body-audit')
checked_package(owner, 'f7bc70fb832f71b51e2a96c618809d688a607936229e79ed00a037a7996e8343', '5b640e1fee4ec01ad533781c2ecc6804249f6d9fd03fcebadc1ea640ebd5d41f')
checked_package(review, sys.argv[1], sys.argv[2])
assert load(review / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'root-execution-declaration-gate.json')['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
source = owner / (NAME + '.lean')
assert sha(source) == '2bbaf50ee3540963968e37202e0fc4a331e5d4063f717feec579966ced81920b'
text = source.read_text()
assert len(text.splitlines()) == 64
assert re.findall(r'^theorem (\w+)', text, re.M) == ['yielded_add', 'done_stable', 'completed_unique']
assert not re.search(r'\b(sorry|axiom|admit|native_decide|set_option)\b', text)
assert re.findall(r'^\s+have (\w+)\s*:', text, re.M) == ['same', 'firstStable', 'secondStable']
assert text.count('induction ') == 2
archive(owner, 'execution-source-v1')
archive(review, 'execution-body-audit')
save('root-execution-body-gate.json', {
    'status': 'ACCEPTED_SOURCE_BODY_FOR_STRICT', 'source_sha256': sha(source), 'lines': 64,
    'root_complete_source_read': True, 'all_exact_contracts_and_IH_retained': True,
    'independent_body_review_sha256': sha(review / 'review.json'),
    'strict_compiler_activation_authorized': True,
    'FULL_activation_authorized': False,
    'default_declaration_limits': True, 'all_linters': True,
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: complete64-line body accepted for sole strict default-limit check')
