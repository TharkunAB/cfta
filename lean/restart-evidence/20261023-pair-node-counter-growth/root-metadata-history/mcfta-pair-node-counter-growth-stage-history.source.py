exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast

owner = Path('/tmp/mcfta-pair-node-counter-growth-closing-preparation')
peer = Path('/tmp/mcfta-pair-node-counter-growth-closing-tool-review')
checked_package(owner, '42b4a62a494fb22e8bf85d72dc81d43e3327242efb2ab5e4f71ca53b6a314013', 'b6e2b2b56bfe79f7c3f0cebaf08f8746724e973c5b703fde665de381e8b234b7')
checked_package(peer, '39c8312ac25add6fb8b2c00effcb9b02704daa33bb6d7db6a7f9d69b0e7d6284', '74187cd168a67e97edfc35e7c861b4f0dc1eef5924d86bcb8ce287bb65d3fa3a')
assert sha(peer / 'review.json') == 'db634fa09d4f3a36004e8ed44f240ba76acee2b0f027f2b2c766cbec76afacbb'
assert load(peer / 'review.json')['status'] == 'CLEAR'
scripts = sorted((owner / 'selected').glob('*.py'))
assert len(scripts) == 5
assert sum(len(path.read_bytes().splitlines()) for path in scripts) == 236
assert sum(sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(path.read_text()))) for path in scripts) == 59
assert (owner / 'selected/verify-seal.py').read_bytes() == (owner / 'basis/verify-seal.py').read_bytes()
archive(owner, 'closing-preparation')
archive(peer, 'closing-template-audit')
save('root-closing-template-gate.json',dict(status='ACCEPTED_PENDING_CLOSING_SOURCE_ONLY',
    module=NAME, root_complete_selected_lines_read=236, selected_assertions=59,
    independent_review_sha256=sha(peer / 'review.json'), all_generic_guards_retained=True,
    ten_metric_slots_still_rejecting=True, actual_binding_and_review_required=True,
    selected_activation_authorized=False))
source = HERE / (NAME + '.lean')
assert sha(source) == '6cfaf5e340d26b8c838f51d93fb3ae0e03b098510ca41b5021ada4e96b72c2e8'
assert source.read_bytes() == (HERE / 'root-body-v1.lean').read_bytes()
assert source.read_bytes() == (HERE / 'root-pair-node-counter-growth-strict-1.source.lean').read_bytes()
variant = HERE / 'variants/v1' / (NAME + '.lean')
assert not variant.exists()
variant.parent.mkdir(parents=True)
variant.write_bytes(source.read_bytes())
save('root-variant-staging.json',dict(status='UNCHANGED_ACTUAL_SELECTED_VARIANT_STAGED',
    variant=str(variant.relative_to(HERE)),source_sha256=sha(variant),source_lines=96,
    body_strict_and_canonical_bytes_equal=True,new_compiler_job=False))
print('Archived pending closing tools and staged the exact selected variant for complete source-history collection.')
