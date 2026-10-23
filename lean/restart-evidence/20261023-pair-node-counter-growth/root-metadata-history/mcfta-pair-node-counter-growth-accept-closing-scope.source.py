exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-pair-node-counter-growth-closing-scope-plan')
peer = Path('/tmp/mcfta-pair-node-counter-growth-closing-scope-audit')
checked_package(owner, 'ba7220e1fa4546e9ee91547c0ce35c4533daa42e8e7e1d62063d7f8d03c77e8d', '5f03547edf0d732dcefcaeffafeb31117f80a1c112b78bb537f79cdfc1e7379b')
checked_package(peer, 'eed9873ad9ea4159d13a43bdfeab5bbaf81af98774abebebaf4ef76dc3a2f1aa', 'db6bfa58789a3aa1e26fafcea71cabf35109958fcbc07fed27e7d5245f96100e')
assert sha(peer / 'review.json') == '72cb57699e785912b988e1776a11f27731f5c8b3ba4f5a277d71c633cc245219'
assert load(peer / 'review.json')['status'] == 'CLEAR'
sources = sorted((owner / 'basis').glob('*.py'))
assert len(sources) == 5
assert sum(len(path.read_bytes().splitlines()) for path in sources) == 236
assert sum(sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(path.read_text()))) for path in sources) == 59
assert len(load(HERE / 'starting-files.json')) == 122017
assert sha(HERE / 'original-sources/Audit.original.lean.txt') == '7bdd945140a975dd1537be82d71ce5e34bf40fc3ceef0df3a9d3d5972d02c4ca'
assert len((HERE / 'original-sources/Audit.original.lean.txt').read_bytes().splitlines()) == 3144
archive(owner, 'closing-scope-plan')
archive(peer, 'closing-scope-audit')
save('root-closing-scope-gate.json', dict(status='ACCEPTED_SOURCE_ONLY_CLOSING_TOOL_SCOPE',
    module=NAME, complete_basis_lines_read=236, baseline_assertions=59,
    all_26_plan_lines_maps_guards_and_59_crosswalk_assertions_read=True,
    selected_target=236, selected_hard_stop=260,
    checkpoint_literal_substitutions_only=True, all_generic_guards_retained=True,
    baseline_files=122017, older_non_Audit_Lean=3654, Haskell=298, active_package=207,
    registry_count=321, registry_entries=1417, override_count=5,
    ten_actual_metric_slots_remain_rejecting=True, mandatory_final_checkpoint_before_seal=True,
    verify_seal_must_remain_byte_identical=True, no_network=True,
    independent_review_sha256=sha(peer / 'review.json'),
    selected_authoring_authorized=True, selected_activation_authorized=False,
    actual_binding_requires_observed_Audit_and_history=True))
print('Accepted closing source-only scope; exact actual data and independent selected review remain required.')
