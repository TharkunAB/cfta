import datetime
import hashlib
import json
import sys
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-deletion-soundness')
expected = sys.argv[1]
review = here / 'final-doc-audit/review.md'
digest = hashlib.sha256(review.read_bytes()).hexdigest()
assert digest == expected
components = json.loads((here / 'archived-components.json').read_text())
historical = json.loads((here / 'verification.json').read_text())
assert historical['status'] == 'PASS'
assert historical['archived_components'] + 1 == len(components) and 'final-doc-audit' in components
record = dict(status='ROOT_FINAL_REVIEW_CLEAR_PRESEAL',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    independent_review='final-doc-audit/review.md', independent_review_sha256=digest,
    root_read_complete_final_review=True,
    historical_first_preservation_components=historical['archived_components'],
    current_components=len(components), component_names=list(components),
    mandatory_final_saved_verification_and_preservation_rerun_pending=True,
    support_archive_pending=True, seal_pending=True, local_publication_pending=True,
    whole_goal_complete=False)
assert not (here / 'root-final-review.json').exists()
(here / 'root-final-review.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(dict(status='PASS', final_components=len(components), final_seal_pending=True)))
