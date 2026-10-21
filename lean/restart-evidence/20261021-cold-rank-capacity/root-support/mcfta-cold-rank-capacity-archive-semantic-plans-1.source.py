import datetime
import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261021-cold-rank-capacity'
for source, destination, verifier in [
    ('/tmp/mcfta-cold-rank-semantic-next-plan', 'semantic-next-plan', 'verify.py'),
    ('/tmp/mcfta-cold-rank-semantic-plan-review', 'semantic-plan-review', 'review-verify.py'),
]:
    subprocess.run(['/usr/bin/python3', str(here / 'archive-component.py'),
                    source, destination, verifier], check=True)
review = dict(status='ROOT_WHOLE_PLAN_AND_ACTUAL_SOURCE_RANGES_REVIEWED',
              sources=17, ranges=20, exact_public_header_lines=30,
              full_semantic_candidate_lines=120,
              candidate_sha256='169ff531a26e38c5b8aea1771237723fccea225b02cb5e3b5de807232c5c8d76',
              new_proof_jobs=0,
              observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
(here / 'semantic-plan-root-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
