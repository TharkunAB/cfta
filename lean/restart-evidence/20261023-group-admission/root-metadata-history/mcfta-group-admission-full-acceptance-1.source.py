exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
import re
import sys
audit = Path('/tmp/mcfta-group-admission-full-audit')
expected_pins,expected_freeze,expected_review = sys.argv[1:]
checked_package(audit,expected_pins,expected_freeze)
assert sha(audit / 'review.json') == expected_review
review = load(audit / 'review.json')
assert review['status'] == 'CLEAR' and not review['ownership']['reviewer_math_author']
assert review['manual_read_scope']['checked_TYPEs_complete'] == ['groups_admitted']
source = HERE / (NAME + '.lean')
assert sha(source) == '1663238beb7983e2d869730cef3c6c32a02992eb54f4638a9d774b7af2a8ece8'
assert load(HERE / 'FULL1.json')['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
readback_path = HERE / 'public-readback/group-admission-full-readback.json'
report = load(readback_path)
head = report['heads'][0]
assert head['checked_type_sha256'] == '99c001a8e52b6d2fe09106432ac76c7f954ebf7b9e505f568648253c39713b8c'
prefix = HERE / 'public-readback/group-admission-groups_admitted-'
checked,printed,body,axioms = [(Path(str(prefix)+part+'.txt')).read_bytes() for part in ['public-type','printed-public-type','body','axioms']]
assert checked == printed and len(checked) == 70177 and len(checked.splitlines()) == 832
assert checked.count(b'\n') == 831 and not checked.endswith(b'\n')
raw = (HERE / 'FULL1.log').read_bytes()
fullname = b'MicroCFTA.SourceCurrentOriginalRowGroupAdmission.groups_admitted'
pattern = re.escape(fullname) + rb'(?:\.\{[^}\n]*\})? :'
first = re.match(rb'@?' + pattern,raw)
declaration = re.search(rb'\ntheorem ' + pattern,raw)
assert first and declaration
assert first.group() + checked + declaration.group() + printed + b' :=\n' + body + axioms == raw
assert review['metrics']['groups_admitted']['checked_type']['sha256'] == head['checked_type_sha256']
target = ROOT / ('lean/MicroCFTA/' + NAME + '.lean')
assert not target.exists()
original_audit = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
audit_path = ROOT / 'lean/MicroCFTA/Audit.lean'
assert audit_path.read_bytes() == original_audit
addition = ('import MicroCFTA.' + NAME + '\n').encode()
assert addition not in original_audit
archive(audit,'full-audit')
target.write_bytes(source.read_bytes())
audit_path.write_bytes(addition + original_audit)
save('selected-sources.json',{str(target.relative_to(ROOT)):dict(sha256=sha(source),lines=100,strict='strict1',full='FULL1')})
save('frozen-modules.json',{NAME:sha(source)})
save('root-full-review.json',dict(status='ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED',module=NAME,
    source_sha256=sha(source),source_lines=100,root_manual_complete_TYPEs=True,
    independent_complete_TYPE_review_sha256=expected_review,
    TYPEs={'groups_admitted':dict(sha256=head['checked_type_sha256'],bytes=len(checked),logical_lines=832,actual_axioms=head['actual_axioms'])},
    readback_sha256=sha(readback_path),BODY_review=dict(complete_retention=True,programmatic_only=True,whole_body_manual_read_claimed=False),
    root_complete_TYPE_read_cuts=[[1,200],[201,400],[401,600],[601,800],[801,832]],
    entire_raw_reconstructed_programmatically=True,goal_status='ACTIVE_INCOMPLETE',
    scope=dict(same_supplied_H22_chain=True,all_boundary_At_and_canonical_admission_derived=True,
        fixed_source_model_ranked_holds=True,future_resource_or_result_oracle=False,new_execution_producer=False,
        generated_root_admission_claimed=False,public_pass_claimed=False,haskell_refinement_claimed=False,whole_goal_complete=False)))
save('root-cohort-audit-gate.json',dict(status='ACCEPTED_INSTALLED_SOURCE_FOR_SOLE_AGGREGATE_AUDIT',
    selected_modules=1,public_theorems=1,source_sha256=sha(source),all_complete_public_TYPEs_reviewed=True,
    root_full_review_sha256=sha(HERE / 'root-full-review.json'),original_Audit_exact_inverse=True,
    compiler_activation_authorized=True,new_imports=1))
print('ACCEPTED complete actual public TYPE; installed exact source and one Audit import.')
