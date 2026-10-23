exec(compile(open('/tmp/mcfta-scan-node-counter-growth-root-common.py').read(), 'root-common.py', 'exec'))
import ast

peer = Path('/tmp/mcfta-scan-node-counter-growth-push-review')
checked_package(peer, 'c808a3f14bd13306743a7d4371a6704173d7e58a3fb7b692caa95c73a58a50fa',
                'ce2ea4fa616b5dcd03ae86fdb6c023a15bd0a4f3e8ddc80d175f00384dcddb61')
assert sha(peer / 'review.json') == 'dab4151469ebedb292697a55205e5a0b0524674ddb9ba29302c52ed90d0a8b2f'
assert load(peer / 'review.json')['status'] == 'CLEAR'
source = Path('/tmp/mcfta-scan-node-counter-growth-authorized-push.py')
basis = Path('/tmp/mcfta-pair-node-counter-growth-authorized-push-1.source.py')
assert source.read_bytes() == (peer / 'selected/authorized-push.py').read_bytes()
assert basis.read_bytes() == (peer / 'basis/authorized-push.py').read_bytes()
assert basis.read_bytes().count(b'pair-node-counter-growth') == 4
assert source.read_bytes() == basis.read_bytes().replace(b'pair-node-counter-growth', b'scan-node-counter-growth')
assert len(source.read_text().splitlines()) == 29
assert sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(source.read_text()))) == 11
assert sha(source) == 'd7798014e96d4342ee040b40fed66ad81e00503a070887f18c5b4ffeb9cfe7b5'
assert Path('/tmp/mcfta-scan-node-counter-growth-root-common.py').read_bytes() == (HERE / 'root-common.py').read_bytes()
assert load(HERE / 'publication-gate.json')['status'] == 'ROOT_ACCEPTED'
assert not (HERE / 'SHA256SUMS').exists()
archive(peer, 'authorized-push-source-audit')
save('root-authorized-push-source-review.json', {
    'status': 'ACCEPTED_WHOLE_PREFIX_ONLY_PUSH_WRAPPER', 'source_sha256': sha(source),
    'lines': 29, 'assertions': 11, 'exact_prefix_substitutions': 4,
    'independent_review_sha256': sha(peer / 'review.json'),
    'explicit_standing_user_authorization': True,
    'destination': 'git@github.com:TharkunAB/cfta.git', 'reference': 'refs/heads/formalize',
    'required_runtime_order': ['final support capture', 'final checkpoint and seal',
                               'clean local publication', 'push and remote verification'],
    'future_seal_publication_or_push_success_claimed': False})
print('PASS: exact authorized push source accepted; final local checks remain required.')
