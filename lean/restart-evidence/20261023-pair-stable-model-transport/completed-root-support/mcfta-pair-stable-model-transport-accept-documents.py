import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
AUDIT = Path('/tmp/mcfta-pair-stable-model-transport-final-doc-audit')
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path):
    return json.loads(path.read_bytes())

assert sha(AUDIT / 'review.json') == sys.argv[1] and load(AUDIT / 'review.json')['status'] == 'CLEAR'
assert (AUDIT / 'FROZEN.json').exists()
pins = load(AUDIT / 'pins.json')
if isinstance(pins, dict):
    pins = [dict(path=name, **pin) for name, pin in pins.items()]
for pin in pins:
    path = AUDIT / pin['path']
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], path
verification = load(HERE / 'verification.json')
preserved = load(HERE / 'preservation-final.json')
assert verification['status'] == preserved['status'] == 'PASS'
assert preserved['baseline_files'] == 100056 and preserved['unchanged_older_non_audit_sources'] == 3639
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
assert preserved['haskell_fix_registry_first_and_retained'] is True
assert verification['actual_jobs'] == 3 and verification['failed_jobs'] == 0
assert verification['audit_build_jobs'] == 3641 and verification['audit_dependencies'] == 75502
subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(AUDIT), 'final-doc-audit'], check=True)
review = dict(status='ROOT_FINAL_DOCUMENT_REVIEW_CLEAR', proof=(HERE / 'proof-commit.txt').read_text().strip(),
    root_read_scope='Complete actual focused note and NEXT-TARGET, current update, FINDINGS repair index and update, source41/TYPE209, normal/live reports and preservation scalar report. All nine original document inverses verified.',
    independent_review='final-doc-audit/review.json', independent_review_sha256=sha(AUDIT / 'review.json'),
    haskell_repairs_added=0, haskell_repair_index_first=True,
    next_scope='Derive all-cell captured request admission through actual same-symbol comparison execution. Keep native Covered and generated-root resources separate.',
    whole_goal_complete=False, seal_or_network_publication_success_claimed=False)
(HERE / 'root-final-doc-review.json').write_text(json.dumps(review, indent=2) + '\n')
publication = dict(status='ROOT_ACCEPTED', publication_scope='LOCAL_ONLY',
    network_publication='AUTHORIZED_PENDING_ROOT_PUSH', proof_commit=review['proof'],
    destination='git@github.com:TharkunAB/cfta.git', ref='refs/heads/formalize',
    root_and_independent_document_reviews='CLEAR', mandatory_seal_verification_required=True, whole_goal_complete=False)
assert not (HERE / 'publication-gate.json').exists()
(HERE / 'publication-gate.json').write_text(json.dumps(publication, indent=2) + '\n')
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Goal turn outcome\n\nThis goal turn is PROGRESS. H24 adds the checked same-Wrapper finite model transport theorem.\nThe exact public TYPE and all actual proof evidence pass root and independent review.\nThe next actual admission producer has a reviewed source-only route.\nThe whole formalization goal remains ACTIVE. Seal, local publication and authorized push follow this gate.\n')
print(json.dumps(dict(status='PASS', proof=review['proof'], publication_scope='LOCAL_ONLY', network_publication='AUTHORIZED_PENDING_ROOT_PUSH')))
