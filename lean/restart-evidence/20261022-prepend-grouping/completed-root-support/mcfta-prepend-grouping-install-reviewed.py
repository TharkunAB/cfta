import ast
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-prepend-grouping'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
independent = here / 'full-public-audit/review.md'
assert independent.is_file() and 'CLEAR' in independent.read_text()
assert sha(independent.read_bytes()) == 'b68d2fce5e35afdd71031244e83e0c380b2f486f38e637c44bf79dc92b663944'
assert (here / 'root-reader-v2-review.json').is_file()
report = json.loads((here / 'public-readback/prepend-grouping-full-readback.json').read_text())
source = (here / 'SourceCurrentPrependGrouping.lean').read_bytes()
assert sha(source) == '3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba'
assert len(source.splitlines()) == 89 and report['source_sha256'] == sha(source)
assert (here / 'prepend-grouping-strict-3.log').read_bytes() == b''
assert json.loads((here / 'prepend-grouping-public-1.json').read_text())['exit_code'] == 0
raw = (here / 'prepend-grouping-public-1.log').read_bytes()
assert sha(raw) == report['log_sha256'] == '215b81824a227e47375a236476dd83092a5bf1c21a421a85e835bdd3e75e61a8'
heads = report['heads']
review = dict(status='ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT', source_sha256=sha(source), source_lines=89,
    public_heads=[head['head'] for head in heads], complete_public_type_root_review='CLEAR',
    independent_complete_public_type_review='CLEAR', root_read_complete_public_types=True,
    root_printed_type_lexical_identity_verified=True, root_printed_type_byte_identity_verified=False,
    four_private_markers_and_all_helpers_absent_from_type=True,
    raw_type_byte_identity_by_head={head['head'].rsplit('.', 1)[1]:head['check_print_type_byte_identity'] for head in heads},
    types_sha256={head['head'].rsplit('.', 1)[1]:head['checked_type_sha256'] for head in heads},
    full_raw_sha256=sha(raw), actual_axioms_by_head={head['head'].rsplit('.', 1)[1]:head['actual_axioms'] for head in heads},
    body_retained_and_programmatically_checked=True, whole_body_manual_read_claimed=False,
    independent_review_sha256=sha(independent.read_bytes()),
    root_checked_type_scope='All nine complete checked TYPEs and both differing printed TYPEs were read. The other seven printed TYPEs have identical raw bytes.',
    metadata_reader_failure_retained=True, metadata_reader_failures=1)
tree = ast.parse((here / 'proof-verifier-preparation-v2/verify-proofs.py').read_text())
for statement in tree.body:
    if isinstance(statement, ast.Assign) and len(statement.targets) == 1 and isinstance(statement.targets[0], ast.Name):
        key = statement.targets[0].id
        if key in {'required_true','required_false'}:
            for name in ast.literal_eval(statement.value):
                review[name] = key == 'required_true'
assert sum(review['raw_type_byte_identity_by_head'].values()) == 7
assert len(review['public_heads']) == 9
(here / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
relative = 'lean/MicroCFTA/SourceCurrentPrependGrouping.lean'
target = root / relative
assert not target.exists()
snapshot = here / 'selected-sources/SourceCurrentPrependGrouping.lean'
snapshot.parent.mkdir()
snapshot.write_bytes(source)
gate = dict(status='ROOT_ACCEPTED', path=relative, sha256=sha(source), lines=89, snapshot='selected-sources/SourceCurrentPrependGrouping.lean')
(here / 'selected-source-gate.json').write_text(json.dumps(gate, indent=2) + '\n')
(here / 'selected-sources.json').write_text(json.dumps({relative:dict(sha256=sha(source),lines=89,strict='prepend-grouping-strict-3',full='prepend-grouping-public-1')}, indent=2) + '\n')
(here / 'frozen-modules.json').write_text(json.dumps({'SourceCurrentPrependGrouping':sha(source)}, indent=2) + '\n')
audit = root / 'lean/MicroCFTA/Audit.lean'
original = (here / 'original-sources/Audit.original.lean.txt').read_bytes()
assert audit.read_bytes() == original and sha(original) == '69e0e42c6e36fbe4cf9868df0582642fe2bf2a6df7c1ad3af4fae169445f6dd3'
addition = b'import MicroCFTA.SourceCurrentPrependGrouping\n'
offset = original.index(b'/-!')
changed = original[:offset] + addition + original[offset:]
assert changed.replace(addition, b'', 1) == original
target.write_bytes(source)
audit.write_bytes(changed)
print(json.dumps(dict(status='PASS', selected_source_sha256=sha(source), source_lines=89, official_install=True, audit_only_new_import=True, audit_outcome='PENDING')))
