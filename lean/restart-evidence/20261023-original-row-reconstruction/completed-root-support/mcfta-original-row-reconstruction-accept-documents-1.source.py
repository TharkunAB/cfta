import hashlib
import json
import runpy
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261023-original-row-reconstruction'
audit = Path('/tmp/mcfta-original-row-reconstruction-final-doc-audit-compact')
digest = lambda data: hashlib.sha256(data).hexdigest()
load = lambda path: json.loads(path.read_bytes())
assert (audit / 'FROZEN.json').is_file()
pins = load(audit / 'pins.json')
rows = pins if isinstance(pins, list) else [dict(path=path, **item) for path, item in pins.items()]
for item in rows:
    data = (audit / item['path']).read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256']
assert load(audit / 'review.json')['status'] == 'CLEAR'
verification = load(here / 'verification.json')
preserved = load(here / 'preservation-final.json')
assert verification['status'] == preserved['status'] == 'PASS'
assert preserved['baseline_files'] == 98415 and preserved['unchanged_haskell_files'] == 298
assert preserved['unchanged_package_files'] == 207 and preserved['unchanged_older_non_audit_sources'] == 3638
assert preserved['haskell_fix_registry_first_and_retained'] is True
assert verification['actual_jobs'] == 4 and verification['failed_jobs'] == 1
assert verification['audit_build_jobs'] == 3640 and verification['audit_dependencies'] == 75501
sys.argv = ['archive-extra.py', str(audit), 'final-doc-audit']
runpy.run_path(str(here / 'archive-extra.py'), run_name='__main__')
review = dict(status='ROOT_FINAL_DOCUMENT_REVIEW_CLEAR',
    proof=(here / 'proof-commit.txt').read_text().strip(),
    root_read_scope='Complete actual focused note and NEXT-TARGET, current update, current FINDINGS repair index and update, complete current source/TYPE, normal/live reports, preservation scalar report. All nine old document inverses verified.',
    independent_review='final-doc-audit/review.json',
    independent_review_sha256=digest((audit / 'review.json').read_bytes()),
    haskell_repairs_added=0, haskell_repair_index_first=True,
    next_scope='Same populated wrapper model/rank transport; explicit genuine old captured request admission. Native all-phase coverage remains separate.',
    whole_goal_complete=False, seal_or_network_publication_success_claimed=False)
(here / 'root-final-doc-review.json').write_text(json.dumps(review, indent=2) + '\n')
publication = dict(status='ROOT_ACCEPTED', publication_scope='LOCAL_ONLY',
    network_publication='AUTHORIZED_PENDING_ROOT_PUSH', proof_commit=review['proof'],
    destination='git@github.com:TharkunAB/cfta.git', ref='refs/heads/formalize',
    root_and_independent_document_reviews='CLEAR',
    mandatory_seal_verification_required=True, whole_goal_complete=False)
assert not (here / 'publication-gate.json').exists()
(here / 'publication-gate.json').write_text(json.dumps(publication, indent=2) + '\n')
print(json.dumps(dict(status='PASS', proof=review['proof'], publication_scope='LOCAL_ONLY',
    network_publication='AUTHORIZED_PENDING_ROOT_PUSH')))
