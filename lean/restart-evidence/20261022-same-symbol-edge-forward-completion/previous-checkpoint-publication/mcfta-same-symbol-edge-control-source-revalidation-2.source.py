import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PLAN = HERE / 'control-author-audit'
index = json.loads((PLAN / 'reviewed-source-index.json').read_text())
SNAPSHOTS = PLAN / 'reviewed-header-v2'
assert index['source_count'] == 18 and index['range_count'] == 37
ranges = 0
for source in index['sources']:
    live = (ROOT / source['path']).read_bytes()
    assert live == (SNAPSHOTS / source['snapshot']).read_bytes()
    assert len(live) == source['bytes']
    assert hashlib.sha256(live).hexdigest() == source['sha256']
    lines = live.splitlines(keepends=True)
    assert len(lines) == source['lines']
    for cut in source['reviewed_ranges']:
        assert 1 <= cut['start'] <= cut['end'] <= len(lines)
        data = b''.join(lines[cut['start'] - 1:cut['end']])
        assert data == (SNAPSHOTS / cut['snapshot']).read_bytes()
        assert len(data) == cut['bytes']
        assert hashlib.sha256(data).hexdigest() == cut['sha256']
        ranges += 1
assert ranges == 37 and len(index['sources']) == 18
report = dict(status='PASS', live_sources=18, exact_ranges=ranges,
    new_Lean_Lake_jobs=0, source_only=True,
    implementation_authorized=False, compiler_authorized=False)
(HERE / 'control-source-revalidation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
