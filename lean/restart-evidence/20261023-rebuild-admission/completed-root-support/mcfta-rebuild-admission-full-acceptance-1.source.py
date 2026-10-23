exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
import re
audit = Path('/tmp/mcfta-rebuild-admission-full-audit')
checked_package(audit, 'bb821c5e706aad0416d0c22f704ee77ceb3424cd0ec506ba1b1594cd5203b962', '9a60c4ba28b4dfcc0aecb1c535e99913bf8080dd731ba5ccf55b8326fce42a31')
expected_review = 'cdd4dd61c7f3d9a38d8f30834762c2eef7f79702554e2c20d2bdcba68c5ee46e'
assert sha(audit / 'review.json') == expected_review
review = load(audit / 'review.json')
assert review['status'] == 'CLEAR' and not review['ownership']['reviewer_math_author']
assert review['manual_read_scope']['checked_TYPEs_complete'] == ['rebuilt_admitted']
source = HERE / (NAME + '.lean')
assert sha(source) == '355224ff767c10856684db24c0d6393e61c63a6754ae6044bb64ba29b0ca61e7'
assert load(HERE / 'FULL1.json')['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
readback_path = HERE / 'public-readback/rebuild-admission-full-readback.json'
head = load(readback_path)['heads'][0]
assert head['checked_type_sha256'] == '614997473b32eebb45689ec80a3e7610065adcb7117268e39b0036978e715fe7'
prefix = HERE / 'public-readback/rebuild-admission-rebuilt_admitted-'
checked, printed, body, axioms = [(Path(str(prefix) + part + '.txt')).read_bytes() for part in ['public-type', 'printed-public-type', 'body', 'axioms']]
assert checked == printed and len(checked) == 90039 and len(checked.splitlines()) == 1052
assert checked.count(b'\n') == 1051 and not checked.endswith(b'\n')
raw = (HERE / 'FULL1.log').read_bytes()
fullname = b'MicroCFTA.SourceCurrentOriginalRowRebuildAdmission.rebuilt_admitted'
pattern = re.escape(fullname) + rb'(?:\.\{[^}\n]*\})? :'
first = re.match(rb'@?' + pattern, raw)
declaration = re.search(rb'\ntheorem ' + pattern, raw)
assert first and declaration
assert first.group() + checked + declaration.group() + printed + b' :=\n' + body + axioms == raw
assert review['metrics']['rebuilt_admitted']['checked_type']['sha256'] == head['checked_type_sha256']
target = ROOT / ('lean/MicroCFTA/' + NAME + '.lean')
assert not target.exists()
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
audit_path = ROOT / 'lean/MicroCFTA/Audit.lean'
assert audit_path.read_bytes() == original_audit
addition = ('import MicroCFTA.' + NAME + '\n').encode()
assert addition not in original_audit
archive(audit, 'full-audit')
target.write_bytes(source.read_bytes())
audit_path.write_bytes(addition + original_audit)
save('selected-sources.json', {str(target.relative_to(ROOT)):dict(sha256=sha(source), lines=90, strict='strict1', full='FULL1')})
save('frozen-modules.json', {NAME:sha(source)})
save('root-full-review.json', dict(status='ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED', module=NAME,
    source_sha256=sha(source), source_lines=90, root_manual_complete_TYPEs=True,
    independent_complete_TYPE_review_sha256=expected_review,
    TYPEs={'rebuilt_admitted':dict(sha256=head['checked_type_sha256'], bytes=len(checked), logical_lines=1052, actual_axioms=head['actual_axioms'])},
    readback_sha256=sha(readback_path), BODY_review=dict(complete_retention=True, programmatic_only=True, whole_body_manual_read_claimed=False),
    root_complete_TYPE_read_cuts=[[1,200],[201,400],[401,600],[601,800],[801,1052]],
    entire_raw_reconstructed_programmatically=True, goal_status='ACTIVE_INCOMPLETE',
    scope=dict(same_literal_H23_heap_only_after=True, same_supplied_H22_chain=True,
        fixed_inventory_source_model_ranked_holds=True, native_Covered_rebuilt_from_request_fields=True,
        explicit_final_Contextual_growth_history_arrows=True, new_execution_producer=False,
        generated_root_old_model_admission_claimed=False, new_source_room_or_resource_producer=False,
        public_pass_claimed=False, haskell_refinement_claimed=False, whole_goal_complete=False)))
save('root-cohort-audit-gate.json', dict(status='ACCEPTED_INSTALLED_SOURCE_FOR_SOLE_AGGREGATE_AUDIT',
    selected_modules=1, public_theorems=1, source_sha256=sha(source), all_complete_public_TYPEs_reviewed=True,
    root_full_review_sha256=sha(HERE / 'root-full-review.json'), original_Audit_exact_inverse=True,
    compiler_activation_authorized=True, new_imports=1))
print('ACCEPTED complete actual public TYPE; installed exact source and one Audit import.')
