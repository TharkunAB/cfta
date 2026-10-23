exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import re
import sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
package = Path('/tmp/mcfta-native-node-counter-growth-full-type-audit')
checked_package(package, expected_pins, expected_freeze)
assert sha(package / 'review.json') == expected_review
review = load(package / 'review.json')
shorts = ['step_mono', 'execute_mono', 'resume_mono']
assert review['status'] == 'CLEAR' and not review['ownership']['reviewer_math_author']
assert review['manual_read_scope']['checked_TYPEs_complete'] == shorts
source = HERE / (NAME + '.lean')
assert sha(source) == 'b43e0c75517bb57db8a062d45c2282c9117ce3944d5086d323318790a8fb9bec'
assert load(HERE / 'FULL1.json')['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
readback_path = HERE / 'public-readback/native-node-counter-growth-full-readback.json'
heads = load(readback_path)['heads']
assert len(heads) == 3
raw = (HERE / 'FULL1.log').read_bytes()
assert len(raw) == 214732 and sha(HERE / 'FULL1.log') == '1cbeacaa45274cfec69e71e8bde81cec52da38f9fb1d7b582ab078ee167bda1c'
starts = []
for short in shorts:
    pattern = re.escape(('MicroCFTA.' + NAME + '.' + short).encode()) + rb'(?:\.\{[^}\n]*\})? :'
    found = list(re.finditer(rb'^@?' + pattern, raw, re.M))
    assert len(found) == 1
    starts.append(found[0])
assert starts[0].start() == 0 and [item.start() for item in starts] == sorted(item.start() for item in starts)
reconstructed, types = [], {}
for index, (short, head, lines, identity) in enumerate(zip(shorts, heads, [17, 17, 18], [True, False, False], strict=True)):
    prefix = HERE / ('public-readback/native-node-counter-growth-' + short + '-')
    checked, printed, body, axioms = [Path(str(prefix) + part + '.txt').read_bytes()
        for part in ['public-type', 'printed-public-type', 'body', 'axioms']]
    assert (checked == printed) is identity is head['check_print_type_byte_identity']
    assert re.sub(rb'[ \t\r\n]+', b' ', checked).strip(b' \t\r\n') == re.sub(rb'[ \t\r\n]+', b' ', printed).strip(b' \t\r\n')
    assert len(checked.splitlines()) == lines and checked.count(b'\n') == lines - 1 and not checked.endswith(b'\n')
    assert sha(Path(str(prefix) + 'public-type.txt')) == head['checked_type_sha256']
    assert sha(Path(str(prefix) + 'printed-public-type.txt')) == head['printed_type_sha256']
    assert review['metrics'][short]['checked_type']['sha256'] == head['checked_type_sha256']
    segment = raw[starts[index].end():starts[index + 1].start() if index + 1 < len(starts) else len(raw)]
    name = ('MicroCFTA.' + NAME + '.' + short).encode()
    delimiter = re.search(rb'\ntheorem ' + re.escape(name) + rb'(?:\.\{[^}\n]*\})? :', segment)
    assert delimiter
    reconstructed.append(starts[index].group() + checked + delimiter.group() + printed + b' :=\n' + body + axioms)
    types[short] = dict(sha256=head['checked_type_sha256'], bytes=len(checked), logical_lines=lines,
        actual_axioms=head['actual_axioms'])
assert b''.join(reconstructed) == raw
target = ROOT / ('lean/MicroCFTA/' + NAME + '.lean')
assert not target.exists()
audit_path = ROOT / 'lean/MicroCFTA/Audit.lean'
original = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert audit_path.read_bytes() == original
addition = ('import MicroCFTA.' + NAME + '\n').encode()
assert addition not in original
archive(package, 'full-type-audit')
target.write_bytes(source.read_bytes())
audit_path.write_bytes(addition + original)
save('selected-sources.json', {str(target.relative_to(ROOT)): dict(sha256=sha(source), lines=79, strict='strict1', full='FULL1')})
save('frozen-modules.json', {NAME: sha(source)})
save('root-full-review.json', dict(status='ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED', module=NAME,
    source_sha256=sha(source), source_lines=79, root_manual_complete_TYPEs=True,
    independent_complete_TYPE_review_sha256=expected_review, TYPEs=types, readback_sha256=sha(readback_path),
    BODY_review=dict(complete_retention=True, programmatic_only=True, whole_body_manual_read_claimed=False),
    root_complete_TYPE_read_cuts={short: [[1, lines]] for short, lines in zip(shorts, [17, 17, 18], strict=True)},
    entire_raw_reconstructed_programmatically=True, goal_status='ACTIVE_INCOMPLETE',
    scope=dict(same_actual_native_outcome_machine_heap=True, arbitrary_state_code_width_and_fuel=True,
        yielded_done_failed_blocked=True, node_counter_monotone=True,
        only_DecidableEq_Symbol_and_EdgeKey=True, actual_pending_constructor_heap_retained=True,
        actual_yielded_IH_state_retained=True, Scan_H23_lift_claimed=False,
        fixed_source_counter_order_claimed=False, Room_WordRanges_domain_Trace_or_resources_claimed=False,
        public_pass_claimed=False, haskell_refinement_claimed=False, whole_goal_complete=False)))
save('root-cohort-audit-gate.json', dict(status='ACCEPTED_INSTALLED_SOURCE_FOR_SOLE_AGGREGATE_AUDIT',
    selected_modules=1, public_theorems=3, source_sha256=sha(source), all_complete_public_TYPEs_reviewed=True,
    root_full_review_sha256=sha(HERE / 'root-full-review.json'), original_Audit_exact_inverse=True,
    compiler_activation_authorized=True, new_imports=1))
print('Accepted all three complete actual public types. Installed the exact source and sole Audit import.')
