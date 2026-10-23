exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
import re
import sys
audit = Path('/tmp/mcfta-pair-inventory-rebase-full-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(audit, expected_pins, expected_freeze)
assert sha(audit / 'review.json') == expected_review
review = load(audit / 'review.json')
assert review['status'] == 'CLEAR' and not review['ownership']['reviewer_math_author']
assert review['manual_read_scope']['checked_TYPEs_complete'] == ['rebase']
source = HERE / (NAME + '.lean')
assert sha(source) == 'b7351e92c6981f5caa5d7a18a05676912b9ee741c94cc2a39f1ba3ef74b03840'
assert load(HERE / 'FULL1.json')['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
readback_path = HERE / 'public-readback/pair-inventory-rebase-full-readback.json'
head = load(readback_path)['heads'][0]
assert head['checked_type_sha256'] == 'acd254913309fc8a7e5fd54719dcf6625fbe40d7a8673022677e3a02312acbf3'
prefix = HERE / 'public-readback/pair-inventory-rebase-rebase-'
checked, printed, body, axioms = [(Path(str(prefix) + part + '.txt')).read_bytes() for part in ['public-type', 'printed-public-type', 'body', 'axioms']]
assert checked == printed and len(checked) == 48948 and len(checked.splitlines()) == 652
assert checked.count(b'\n') == 651 and not checked.endswith(b'\n')
raw = (HERE / 'FULL1.log').read_bytes()
fullname = b'MicroCFTA.SourceCurrentAllocatedNativePairInventoryRebase.rebase'
pattern = re.escape(fullname) + rb'(?:\.\{[^}\n]*\})? :'
first = re.match(rb'@?' + pattern, raw)
declaration = re.search(rb'\ntheorem ' + pattern, raw)
assert first and declaration
assert first.group() + checked + declaration.group() + printed + b' :=\n' + body + axioms == raw
assert review['metrics']['rebase']['checked_type']['sha256'] == head['checked_type_sha256']
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
save('selected-sources.json', {str(target.relative_to(ROOT)):dict(sha256=sha(source), lines=77, strict='strict1', full='FULL1')})
save('frozen-modules.json', {NAME:sha(source)})
save('root-full-review.json', dict(status='ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED', module=NAME,
    source_sha256=sha(source), source_lines=77, root_manual_complete_TYPEs=True,
    independent_complete_TYPE_review_sha256=expected_review,
    TYPEs={'rebase':dict(sha256=head['checked_type_sha256'], bytes=len(checked), logical_lines=652, actual_axioms=head['actual_axioms'])},
    readback_sha256=sha(readback_path), BODY_review=dict(complete_retention=True, programmatic_only=True, whole_body_manual_read_claimed=False),
    root_complete_TYPE_read_cuts=[[1,220],[221,440],[441,652]],
    entire_raw_reconstructed_programmatically=True, goal_status='ACTIVE_INCOMPLETE',
    scope=dict(same_full_wrapper=True, computed_next_source_is_current_heap=True,
        computed_next_roots_append_operands=True, native_At_pair_Stable_and_canonical_admission=True,
        derived_Agreement_old_valid_and_exact_ranks=True, exact_operand_input_validity=True,
        new_execution_producer=False, new_source_room_or_resource_producer=False,
        original_global_domain_Trace_transport_claimed=False, strict_valid_domain_growth_claimed=False,
        public_pass_claimed=False, haskell_refinement_claimed=False, whole_goal_complete=False)))
save('root-cohort-audit-gate.json', dict(status='ACCEPTED_INSTALLED_SOURCE_FOR_SOLE_AGGREGATE_AUDIT',
    selected_modules=1, public_theorems=1, source_sha256=sha(source), all_complete_public_TYPEs_reviewed=True,
    root_full_review_sha256=sha(HERE / 'root-full-review.json'), original_Audit_exact_inverse=True,
    compiler_activation_authorized=True, new_imports=1))
print('ACCEPTED complete actual public TYPE; installed exact77-line source and one Audit import.')
