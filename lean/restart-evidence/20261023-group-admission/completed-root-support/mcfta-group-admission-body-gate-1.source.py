exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
import re
plan = Path('/tmp/mcfta-group-admission-declaration-plan')
checked_package(plan, 'd13ed06d393b4c6f1d95dd391e2890b3c723cfcffe4f2397ecc21374baa93dd5', 'e525c308510452610ecd0778a2f956f045e35aeb00a3bb7b66cbd85c4a0c315a')
declarations = Path('/tmp/mcfta-group-admission-declaration-audit')
checked_package(declarations, 'da7edfc54bb700d40dafdd8f7a9adc456aa9badbacc3860c36ebfdcb3edf6910', '622b1e585ff2079085da06195567681e630cf56ad4896e9bf67fd6b1e6989e9b')
owner = Path('/tmp/mcfta-group-admission-source-v1')
checked_package(owner, 'c1f60d66eef3c88047a11908ebbc16fbeee0102d0850c0b66859ba3e205297de', '3f80545375257edb0f12d1afb2a314ee30849e12dd53d717c3ee70923e1d2e58')
audit = Path('/tmp/mcfta-group-admission-body-v1-audit')
checked_package(audit, '978339e2167e09f55f32e7533891f1e6aabc8e10401ddff268b44f52c0963f65', '26ad505fd5d42855793c7503a057b6cd39df6489deaa79aa0fba88232056144a')
assert load(audit / 'review.json')['status'] == load(declarations / 'review.json')['status'] == 'CLEAR'
selected = owner / (NAME + '.lean')
assert sha(selected) == '1663238beb7983e2d869730cef3c6c32a02992eb54f4638a9d774b7af2a8ece8'
source = selected.read_bytes()
assert len(source.splitlines()) == 100 and source.endswith(('end MicroCFTA.' + NAME + '\n').encode())
positions = []
for item in load(plan / 'insertion-map.json')['compiled_fragments']:
    fragment = (plan / item['file']).read_bytes()
    if 'future_body_attachment' in item:
        fragment = fragment.rstrip(b'\n') + item['future_body_attachment'].encode()
    assert source.count(fragment) == 1, item['file']
    positions.append(source.index(fragment))
assert positions == sorted(positions) and len(set(positions)) == 10
header = (plan / 'public-header.lean.txt').read_bytes().rstrip(b'\n') + b' := by\n'
body = source.split(header,1)[1]
assert re.findall(rb'\bhave\s+(\w+)\s*:', body) == [b'reversed',b'included',b'found',b'contents']
assert body.count(b'obtain ') == 2 and body.count(b'refine Fin.induction ?_ ?_') == 1
assert not re.search(rb'\b(?:sorry|admit|axiom|native_decide|set_option|let|show|suffices|haveI|letI)\b',body)
assert re.findall(rb'(?m)^theorem (\w+)',source) == [b'groups_admitted']
for path,name in [(plan,'declaration-plan'),(declarations,'declaration-audit'),(owner,'source-v1'),(audit,'body-v1-audit')]:
    archive(path,name)
for path,name in [(Path('/tmp/mcfta-group-admission-route-assessment'),'route-assessment')]:
    checked_package(path,'cfc9401bd94fa31aaf1b31fb0fc7718337b8423cadbe7287710d90c37a72f976','49a00175e7fe49d1031cac42fb573aa2c1e89d4a5c0da316fae75f3a00bc26f2')
    archive(path,name)
(HERE / 'root-declaration-gate.json').write_bytes((owner / 'root-declaration-gate.json').read_bytes())
(HERE / (NAME + '.lean')).write_bytes(source)
save('root-v1-body-gate.json',dict(status='ACCEPTED_COMPLETE_BODY_FOR_STRICT_CHECK',
    module=NAME, source_sha256=sha(selected), source_lines=100, whole_source_hard_stop=180,
    exact_declaration_gate_sha256=sha(owner / 'root-declaration-gate.json'),
    independent_body_review_sha256=sha(audit / 'review.json'), root_complete_source_lines_read=100,
    all_ten_fragments_exact=True, local_haves=4, local_obtains=2, generated_Fin_IH_reviewed=True,
    default_declaration_limits=True, all_linters=True, compiler_activation_authorized=True))
print('ACCEPTED complete reviewed body for first strict check.')
