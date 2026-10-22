import hashlib
import json
import runpy
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261023-original-row-reconstruction'
owner = Path('/tmp/mcfta-original-row-reconstruction-next-admission-inventory')
audit = Path('/tmp/mcfta-original-row-reconstruction-next-audit')
digest = lambda data: hashlib.sha256(data).hexdigest()
for package in [owner, audit]:
    pins = json.loads((package / 'pins.json').read_bytes())
    rows = pins if isinstance(pins, list) else [dict(path=path, **item) for path, item in pins.items()]
    for item in rows:
        data = (package / item['path']).read_bytes()
        assert len(data) == item['bytes'] and digest(data) == item['sha256']
index = json.loads((owner / 'source-index.json').read_bytes())
assert len(index['sources']) == 13
count = 0
for item in index['sources']:
    snapshot = (owner / item['snapshot']).read_bytes()
    assert snapshot == (root / item['path']).read_bytes() and digest(snapshot) == item['sha256']
    lines = snapshot.splitlines(keepends=True)
    for cut in item['cuts']:
        data = (owner / cut['path']).read_bytes()
        assert data == b''.join(lines[cut['start'] - 1:cut['end']])
        assert digest(data) == cut['sha256'] and len(data.splitlines()) == cut['lines']
        count += 1
assert count == 16
assert digest((audit / 'review.md').read_bytes()) == 'e879eeb33c5a15197bd73139b57a7b54d38226ff21ff912b318a844abb4a4db7'
assert digest((owner / 'proposed-next-contract.txt').read_bytes()) == '63196ef1d93982f578e8a2cdfa8308c5437cc6a7b9f56402564c61703b1da12d'
for package, name in [(owner, 'next-admission-inventory'), (audit, 'next-admission-audit')]:
    sys.argv = ['archive-extra.py', str(package), name]
    runpy.run_path(str(here / 'archive-extra.py'), run_name='__main__')
record = dict(status='ROOT_SOURCE_ONLY_FUTURE_ROUTE_CLEAR', repository_sources=12,
    frozen_historical_proposal_headers=1, exact_indexed_cuts=16, complete_field_supplements=2,
    root_read_scope='Whole note, proposed plain contract, independent review, source index, all16cuts and both supplements. Live identities and cut bytes checked programmatically. No whole-source manual-read claim.',
    future_target='Same populated wrapper Stable transport under finite-input Agreement and genuine old captured canonical-request EdgeInputs.',
    limitations=['Native Covered is a separate operational obligation.',
        'Arbitrary fixed H23 models do not supply a concrete inventory or its At certificate.',
        'WordRanges, fresh key safety and new-source Room/global Trace require separate proofs.'],
    declaration_or_body_approved=False, new_lean_lake_jobs=0, whole_goal_complete=False)
(here / 'root-next-inventory-review.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
