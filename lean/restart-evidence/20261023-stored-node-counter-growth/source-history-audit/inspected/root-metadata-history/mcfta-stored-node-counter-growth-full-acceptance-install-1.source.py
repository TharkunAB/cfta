exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
import re, sys
expected_pins, expected_freeze, expected_review = sys.argv[1:]
package = Path('/tmp/mcfta-stored-node-counter-growth-full-type-audit')
checked_package(package, expected_pins, expected_freeze)
assert sha(package / 'review.json') == expected_review
review = load(package / 'review.json')
shorts = ['execute_mono', 'unfold_mono', 'maybeMu_mono']
assert review['status'] == 'CLEAR' and not review['ownership']['reviewer_math_author']
assert review['manual_read_scope']['checked_TYPEs_complete'] == shorts
source = HERE / (NAME + '.lean')
assert sha(source) == '2dc66e6e7cc728b051a65d622f6aab9bd236ac485b90eb4c1f60650fc438d16a'
assert load(HERE / 'FULL1.json')['exit_code'] == 0 and (HERE / 'strict1.log').read_bytes() == b''
readback_path = HERE / 'public-readback/stored-node-counter-growth-full-readback.json'
heads = load(readback_path)['heads']
assert len(heads) == 3
raw = (HERE / 'FULL1.log').read_bytes()
starts = []
for short in shorts:
    pattern = re.escape(('MicroCFTA.' + NAME + '.' + short).encode()) + rb'(?:\.\{[^}\n]*\})? :'
    found = list(re.finditer(rb'^@?' + pattern, raw, re.M))
    assert len(found) == 1
    starts.append(found[0])
assert starts[0].start() == 0 and [m.start() for m in starts] == sorted(m.start() for m in starts)
reconstructed, types = [], {}
for index, (short, head, lines) in enumerate(zip(shorts, heads, [13, 12, 12], strict=True)):
    prefix = HERE / ('public-readback/stored-node-counter-growth-' + short + '-')
    checked, printed, body, axioms = [Path(str(prefix) + part + '.txt').read_bytes()
        for part in ['public-type', 'printed-public-type', 'body', 'axioms']]
    assert checked == printed and len(checked.splitlines()) == lines
    assert checked.count(b'\n') == lines - 1 and not checked.endswith(b'\n')
    assert sha(Path(str(prefix) + 'public-type.txt')) == head['checked_type_sha256']
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
save('selected-sources.json', {str(target.relative_to(ROOT)): dict(sha256=sha(source), lines=82, strict='strict1', full='FULL1')})
save('frozen-modules.json', {NAME: sha(source)})
save('root-full-review.json', dict(status='ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED', module=NAME,
    source_sha256=sha(source), source_lines=82, root_manual_complete_TYPEs=True,
    independent_complete_TYPE_review_sha256=expected_review, TYPEs=types, readback_sha256=sha(readback_path),
    BODY_review=dict(complete_retention=True, programmatic_only=True, whole_body_manual_read_claimed=False),
    root_complete_TYPE_read_cuts={short: [[1, lines]] for short, lines in zip(shorts, [13, 12, 12], strict=True)},
    entire_raw_reconstructed_programmatically=True, goal_status='ACTIVE_INCOMPLETE',
    scope=dict(same_repaired_executor_outcome_state=True, arbitrary_initial_heaps_and_environment=True,
        done_and_pending=True, node_counter_monotone=True, only_public_DecidableEq_EdgeKey=True,
        callback_bound_derived=True, actual_optional_binder_probes_and_request=True,
        native_Scan_H23_lift_claimed=False, fixed_source_counter_order_claimed=False,
        Room_WordRanges_domain_Trace_or_resources_claimed=False, public_pass_claimed=False,
        haskell_refinement_claimed=False, whole_goal_complete=False)))
save('root-cohort-audit-gate.json', dict(status='ACCEPTED_INSTALLED_SOURCE_FOR_SOLE_AGGREGATE_AUDIT',
    selected_modules=1, public_theorems=3, source_sha256=sha(source), all_complete_public_TYPEs_reviewed=True,
    root_full_review_sha256=sha(HERE / 'root-full-review.json'), original_Audit_exact_inverse=True,
    compiler_activation_authorized=True, new_imports=1))
print('ACCEPTED all complete actual public TYPEs. Installed exact82-line source and sole Audit import.')
