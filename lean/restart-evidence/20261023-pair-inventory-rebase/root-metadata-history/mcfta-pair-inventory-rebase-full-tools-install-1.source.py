exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-pair-inventory-rebase-full-preparation')
review = Path('/tmp/mcfta-pair-inventory-rebase-full-tools-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, 'bb18094111376f0889895c0bf402fe6dc136c618e59b9a6d6cfdbda335dffe71', '6c2f43a3237b2641a39d69d0d617a51759c42f2178b6382e269a9eb38cb7ffcd')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review
assert load(review / 'review.json')['status'] == 'CLEAR'
gate = load(HERE / 'selected-source-gate.json')
assert gate['status'] == 'ACCEPTED_STRICT_SOURCE' and gate['source_lines'] == 77
assert gate['source_sha256'] == 'b7351e92c6981f5caa5d7a18a05676912b9ee741c94cc2a39f1ba3ef74b03840'
assert (HERE / 'strict1.log').read_bytes() == b''
assert not (HERE / (NAME + '.lean')).exists()
archive(owner, 'full-preparation')
archive(review, 'full-tools-audit')
installed = {}
for name, expected in [('check-full-public.py', '0d24fa000eaad73f6413663241494ae72c9946f37df73694894aaeeed30bf3e0'),
        ('prepare-full.py', '386f65a9d2e72c50f58a89cef75ebf848307814fb9b1b9f3656a38ba55a1f64b')]:
    assert sha(owner / 'selected' / name) == expected and not (HERE / name).exists()
    (HERE / name).write_bytes((owner / 'selected' / name).read_bytes())
    installed[name] = sha(HERE / name)
save('root-full-tools-gate.json', dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',
    module=NAME, source_sha256=gate['source_sha256'], public_heads=['rebase'],
    root_whole_selected_and_basis_source_lines_read=203, exact_deltas_read=True,
    independent_review_sha256=expected_review, installed_tools=installed,
    exact_scope_gate_sha256=sha(HERE / 'root-full-tool-scope-gate.json'),
    materializer_activation=True, sole_FULL_activation=True, reader_activation_after_actual_FULL=True,
    mandatory_seven_CLI_inputs_unchanged=True, diagnostic_tail_lines=14,
    all_generic_guards_retained=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED complete203-line tools for once-only materialization and sole FULL on strict77 source.')
