exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
packages = [
    ('route-assessment', 'e96cc47c4d83dae6f85b0d7bd0aab6880182d10233eb3b5211e0c4d18bdf4770', '6c74c8d2703a5f76b483fad645f20413b9598f70e5a9608bd92d9debfd90250b'),
    ('declaration-plan', '53e6f874e224078a4ec6fcdcbf7d43dc467019fdb72cd69a98657e8f7f27c750', '43a1d4f0ee4dfae29cb4640eccfaa53a5910fd1c655353f06df637c22495edc8'),
    ('declaration-audit', 'f2806d4f3a437056df5c9dc86cf5ad98ad2e864a7583f35c722373baf3650f22', '23aca13229152f97f7b36e8efe05e8081dbc5b0f5fc2bcf67f49cd2b1960756f'),
    ('source-v1', 'baf14666b6a6dd779ed995144fd55c351b3a45230c41f31b5aed1c14112e9125', '7f893c1117cfacdd3fb25ea184bc4f9cd5e4caed2360df26f6289fc1c62d3a86'),
    ('body-v1-audit', 'f789c3070e0f0e3fa5d51a87db9a5faf23177ffd2e51e09d6ff4d59d694b348d', '7596dbfd580822da51cf72ac69a1e11713618faee855aeee0f09a465e22247c7')]
for suffix, pins, frozen in packages:
    checked_package(Path('/tmp/mcfta-rebuild-admission-' + suffix), pins, frozen)
gate = Path('/tmp/mcfta-rebuild-admission-root-declaration-gate.json')
assert load(gate)['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
review = Path('/tmp/mcfta-rebuild-admission-body-v1-audit/review.json')
assert load(review)['status'] == 'CLEAR'
assert sha(review) == 'e4f0b898f0977c28c2023a0efe6b77d63249a396998ace75773474fda334e33b'
source = Path('/tmp/mcfta-rebuild-admission-source-v1') / (NAME + '.lean')
assert sha(source) == '355224ff767c10856684db24c0d6393e61c63a6754ae6044bb64ba29b0ca61e7'
assert len(source.read_bytes().splitlines()) == 90
assert git('rev-parse', 'HEAD').strip() == START
push = load(Path('/tmp/mcfta-group-admission-remote-publication.json'))
assert push['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and push['checkpoint'] == START
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentOriginalRowGroupAdmission.lean') == '1663238beb7983e2d869730cef3c6c32a02992eb54f4638a9d774b7af2a8ece8'
assert not (HERE / (NAME + '.lean')).exists() and not (HERE / 'strict-selected-source.lean').exists()
for suffix, _pins, _frozen in packages:
    archive(Path('/tmp/mcfta-rebuild-admission-' + suffix), suffix)
(HERE / 'root-declaration-gate.json').write_bytes(gate.read_bytes())
(HERE / 'strict-selected-source.lean').write_bytes(source.read_bytes())
save('root-v1-body-gate.json', dict(status='ACCEPTED_COMPLETE_BODY_FOR_STRICT_CHECK', module=NAME,
    source_sha256=sha(source), source_lines=90, whole_source_hard_stop=180,
    exact_declaration_gate_sha256=sha(gate), independent_body_review_sha256=sha(review),
    root_complete_source_lines_read=90, all_five_fragments_exact=True,
    public_lets=4, local_haves=0, local_lets=0, local_obtains=1, introduced_arrow_fields=3,
    helper_count=0, induction=False, coverage_rebuilt_from_two_request_fields=True,
    same_literal_H23_after_and_same_H30_chain=True, no_new_oracle_or_local_Extension_premise=True,
    H23_authorship_erratum_retained=True, H30_checkpoint=START, H30_pushed_and_remote_verified=True,
    default_declaration_limits=True, all_linters=True, compiler_activation_authorized=True,
    canonical_module_snapshot_absent_until_materializer=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED exact whole 90-line body for default-limit strict check after completed H30 checkpoint.')
