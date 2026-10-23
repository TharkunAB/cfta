exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
import datetime
plan = Path('/tmp/mcfta-rebuild-admission-declaration-plan')
audit = Path('/tmp/mcfta-rebuild-admission-declaration-audit')
checked_package(plan, '53e6f874e224078a4ec6fcdcbf7d43dc467019fdb72cd69a98657e8f7f27c750', '43a1d4f0ee4dfae29cb4640eccfaa53a5910fd1c655353f06df637c22495edc8')
checked_package(audit, 'f2806d4f3a437056df5c9dc86cf5ad98ad2e864a7583f35c722373baf3650f22', '23aca13229152f97f7b36e8efe05e8081dbc5b0f5fc2bcf67f49cd2b1960756f')
assert sha(audit / 'review.json') == '94a8127cada4d1ec92b0e1c9b6c48b86354047c3a4702c00419eb601965c7957'
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert sha(plan / 'contracts.json') == '7b11160b762f900be57e67e0b930f10ec4848b8372f4e026a12b62158e9e2c55'
assert sha(plan / 'insertion-map.json') == '92c8a8647b3e63ebeeb8b12a667db62ac654017a89a244804db649c9ed248690'
assert sha(ROOT / 'lean/MicroCFTA/SourceCurrentOriginalRowGroupAdmission.lean') == '1663238beb7983e2d869730cef3c6c32a02992eb54f4638a9d774b7af2a8ece8'
path = Path('/tmp/mcfta-rebuild-admission-root-declaration-gate.json')
assert not path.exists()
data = dict(status='ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    module='SourceCurrentOriginalRowRebuildAdmission', public_heads=['rebuilt_admitted'],
    contracts_sha256=sha(plan / 'contracts.json'), insertion_map_sha256=sha(plan / 'insertion-map.json'),
    independent_review_sha256=sha(audit / 'review.json'), root_whole_context_lines_read=28,
    root_whole_public_header_lines_read=50, root_all_public_lets_and_introduced_field_types_read=True,
    compiled_fragments=5, public_lets=4, body_lets=0, body_haves=0, helpers=0, induction=False,
    explicit_intro_fields=3, explicit_obtain_fields=2, whole_source_hard_stop=180,
    default_declaration_limits=True, all_linters=True,
    source_only_body_authoring_accepted=True, compiler_activation_authorized=False,
    compiler_requires_completed_H30_checkpoint=True,
    ownership_erratum_sha256=sha(audit / 'authorship-erratum.md'),
    H23_foundation_author='Arity', H31_declaration_author='Guard', H31_prospective_body_author='Root',
    goal_status='ACTIVE_INCOMPLETE')
path.write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps(data))
