import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

audit = Path('/tmp/mcfta-comparison-native-covered-public-audit')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
readback = load(HERE / 'public-readback/comparison-native-covered-full-readback.json')
assert readback['source_sha256'] == 'c923d6ffba1ccd787aa7384225e34232b5ff3b6098be671355787b982ead3f01'
assert readback['source_lines'] == 204 and readback['owned_public_job_exit'] == 0 and readback['no_omissions']
assert readback['log_bytes'] == 2687112 and readback['log_sha256'] == '01e903addd01f1d88413664ef8eed2664b1236e61387879d22c4c58755d0887e'
head, = readback['heads']
assert head['head'] == 'MicroCFTA.' + NAME + '.original_rows_complete'
assert head['check_print_type_identity'] and head['check_print_type_byte_identity'] and head['check_print_type_lexical_identity']
assert head['checked_type_sha256'] == head['printed_type_sha256'] == '73f30229b7c09cdbfa0ebee0a99d161f66b32089d51e4b6be79bd9a7aeeab485'
assert head['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
checked = (HERE / 'public-readback/comparison-native-covered-original_rows_complete-public-type.txt').read_bytes()
printed = (HERE / 'public-readback/comparison-native-covered-original_rows_complete-printed-public-type.txt').read_bytes()
assert checked == printed and len(checked) == 109969 and len(checked.splitlines()) == 1063 and checked.count(b'\n') == 1062
assert sha(HERE / 'public-readback/comparison-native-covered-original_rows_complete-public-type.txt') == head['checked_type_sha256']
assert not any(marker in checked.decode() for marker in ['_private', '✝', '†', '‡'])
assert (HERE / 'comparison-native-covered-strict-1.log').read_bytes() == b''
assert load(HERE / 'comparison-native-covered-strict-1.json')['exit_code'] == 0
archive(audit, 'public-audit')
save('root-full-review.json', dict(status='ROOT_ACCEPTED',
    complete_public_type_root_review='CLEAR', independent_complete_public_type_review='CLEAR',
    root_printed_type_lexical_identity_verified=True,
    raw_type_byte_identity_by_head={'original_rows_complete': True},
    root_type_read_scope='All1063 logical lines, in five disjoint complete chunks. Only leading ASCII spaces were removed for display. Every TYPE token was retained. Raw checked/printed byte identity was verified programmatically.',
    source_complete_root_and_independent_reviews=True, body_review_scope='Retained and checked programmatically only; no whole BODY manual read.',
    independent_review_sha256=sha(audit / 'review.json'), source_sha256=readback['source_sha256'],
    actual_axioms=head['actual_axioms'], whole_goal_complete=False))
gate = load(HERE / 'selected-source-gate.json')
source = HERE / gate['snapshot']
target = ROOT / gate['path']
assert not target.exists() and sha(source) == readback['source_sha256']
original = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
audit_path = ROOT / 'lean/MicroCFTA/Audit.lean'
assert audit_path.read_bytes() == original and len(original.splitlines()) == 3133
addition = ('import MicroCFTA.' + NAME + '\n').encode()
assert addition not in original
target.write_bytes(source.read_bytes())
audit_path.write_bytes(addition + original)
assert audit_path.read_bytes().replace(addition, b'', 1) == original
save('selected-sources.json', {gate['path']: dict(sha256=sha(source), lines=204,
    strict='comparison-native-covered-strict-1', full='comparison-native-covered-public-1')})
save('frozen-modules.json', {NAME: sha(source)})
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Accepted actual public theorem\n\nStrict1 and the sole FULL1 pass on the unchanged204-line source.\nRoot and independent reviews accept every token of the complete1063-line public TYPE.\nChecked and printed TYPE bytes are identical. Actual axioms are the standard three.\nBODY evidence is programmatic only. The official module and sole new Audit import are installed.\nThe next action is the sole aggregate Audit.\n')
print(json.dumps(dict(status='PASS', installed_module=gate['path'], type_lines=1063, source_lines=204)))
