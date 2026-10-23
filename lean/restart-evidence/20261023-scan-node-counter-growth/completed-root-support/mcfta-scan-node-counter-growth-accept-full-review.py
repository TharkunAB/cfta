exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import re
import sys

peer = Path('/tmp/mcfta-scan-node-counter-growth-public-type-review')
checked_package(peer, sys.argv[1], sys.argv[2])
assert sha(peer / 'review.json') == sys.argv[3]
independent = load(peer / 'review.json')
assert independent['status'] == 'CLEAR' and independent['ownership']['reviewer_math_author'] is False
source = HERE / (NAME + '.lean')
assert sha(source) == '7db9cd645899e31a3f04149e0ea8bd27f8e5c55c336aab872f8c286c04822cb7'
assert len(source.read_bytes().splitlines()) == 80
readback_path = HERE / 'full-readback/scan-node-counter-growth-full-readback.json'
readback = load(readback_path)
assert readback['source_sha256'] == sha(source) and readback['source_lines'] == 80
assert independent['readback_sha256'] == sha(readback_path)
raw = (HERE / 'root-scan-node-counter-growth-full-1.log').read_bytes()
assert len(raw) == readback['log_bytes'] == 656026
assert sha(HERE / 'root-scan-node-counter-growth-full-1.log') == readback['log_sha256'] == independent['FULL_raw_sha256'] == 'c58e38b0e751067b16adffcfaaa9c685ca651a80e3a84382eae067a9a35d704c'
reconstructed = b''
types, cuts = {}, {}
for head in readback['heads']:
    short = head['head'].rsplit('.', 1)[1]
    stem = 'scan-node-counter-growth-' + short
    checked, printed, body, axioms = [(HERE / 'full-readback' / (stem + suffix)).read_bytes()
        for suffix in ['-public-type.txt','-printed-public-type.txt','-body.txt','-axioms.txt']]
    assert re.sub(rb'[ \t\r\n]+',b' ',checked).strip(b' \t\r\n') == re.sub(rb'[ \t\r\n]+',b' ',printed).strip(b' \t\r\n')
    assert head['check_print_type_byte_identity'] is (checked == printed)
    assert head['check_print_type_lexical_identity'] is True
    assert set(head['actual_axioms']) <= {'Classical.choice','Quot.sound','propext'}
    metric = independent['metrics'][short]
    assert metric['checked_type']['sha256'] == head['checked_type_sha256']
    assert metric['actual_raw_byte_identity'] is head['check_print_type_byte_identity']
    assert metric['axioms']['actual'] == head['actual_axioms']
    for spelling in ['_private','✝','†','‡']:
        assert spelling.encode() not in checked + printed
    name = head['head'].encode()
    reconstructed += b'@' + name + b' :' + checked + b'\n' + head['kind'].encode() + b' ' + name + b' :' + printed + b' :=\n' + body + axioms
    types[short] = dict(sha256=head['checked_type_sha256'],bytes=len(checked),logical_lines=len(checked.splitlines()),actual_axioms=head['actual_axioms'])
    cuts[short] = [[1,len(checked.splitlines())]]
assert reconstructed == raw
assert list(types) == ['outcomeState','step_mono','execute_mono']
assert [v['logical_lines'] for v in types.values()] == [2,35,35]
destination = ROOT / 'lean/MicroCFTA' / (NAME + '.lean')
assert not destination.exists()
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
original = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert audit.read_bytes() == original
addition = ('import MicroCFTA.' + NAME + '\n').encode()
assert addition not in original
assert git('rev-parse','HEAD').strip() == START
assert not (HERE / 'variants').exists()
diagnostic = Path('/tmp/mcfta-scan-node-counter-growth-public-type-review-diagnostic.json')
assert sha(diagnostic) == '7c9a93bd4e77e27cab25833e969dc4b3bbe1163cbfdbb48951d8e48986d1355c'
archive(peer, 'public-type-audit')
save('public-type-review-diagnostic.json', load(diagnostic))
save('full-preparation.json', load(Path('/tmp/mcfta-scan-node-counter-growth-materialize-full-1.log')))
destination.write_bytes(source.read_bytes())
audit.write_bytes(addition + original)
variant = HERE / 'variants/v1' / (NAME + '.lean')
variant.parent.mkdir(parents=True)
variant.write_bytes(source.read_bytes())
save('root-variant-staging.json',dict(status='UNCHANGED_ACTUAL_SELECTED_VARIANT_STAGED',
    variant=str(variant.relative_to(HERE)), source_sha256=sha(source), source_lines=80,
    body_strict_and_canonical_bytes_equal=True, new_compiler_job=False))
save('selected-sources.json', {'lean/MicroCFTA/' + NAME + '.lean':dict(sha256=sha(source),lines=80,strict='root-scan-node-counter-growth-strict-1',full='root-scan-node-counter-growth-full-1')})
save('frozen-modules.json', {NAME:sha(source)})
save('root-full-review.json', dict(status='ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED',
    module=NAME, source_sha256=sha(source), source_lines=80, root_manual_complete_TYPEs=True,
    independent_complete_TYPE_review_sha256=sha(peer / 'review.json'), TYPEs=types,
    readback_sha256=sha(readback_path),
    BODY_review=dict(complete_retention=True,programmatic_only=True,whole_body_manual_read_claimed=False),
    root_complete_TYPE_read_cuts=cuts, entire_raw_reconstructed_programmatically=True,
    goal_status='ACTIVE_INCOMPLETE', scope=dict(
        same_actual_scan_outcome_checked_native_machine_heap=True,
        arbitrary_state_control_width_and_fuel=True,
        yielded_done_failed_constraintError_blocked=True, node_counter_monotone=True,
        accessor_total_full_state_without_instances=True,
        only_DecidableEq_Symbol_and_EdgeKey_on_theorems=True,
        actual_yielded_IH_state_retained=True, H23_counter_lift_claimed=False,
        fixed_source_counter_order_claimed=False, upper_bounds_Room_WordRanges_domain_Trace_or_resources_claimed=False,
        public_pass_claimed=False, haskell_refinement_claimed=False, whole_goal_complete=False)))
print('PASS: all complete actual public TYPEs accepted; one source and one Audit import installed.')
