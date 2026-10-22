import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
old = HERE / 'drafts/SourceCurrentAllocatedDirectEdgeWordRanges.source.lean.txt'
new = HERE / 'drafts/SourceCurrentAllocatedDirectEdgeWordRanges.source-v2.lean.txt'
before = old.read_bytes()
assert len(before.splitlines()) == 44
assert before.count(b'fun after value => EdgeResident after.heap value') == 1
after = before.replace(b'fun after value => EdgeResident after.heap value',
                       b'fun after value => InternedEdgeResidency.EdgeResident after.heap value', 1)
assert not new.exists()
new.write_bytes(after)
(HERE / 'drafts/source-qualification.patch').write_text(''.join(difflib.unified_diff(
    before.decode().splitlines(True), after.decode().splitlines(True),
    fromfile=old.name, tofile=new.name)))
report = {'status': 'PRECHECK_SOURCE_REPAIR', 'proof_commands_executed': 0,
          'reason': 'The exact context does not open InternedEdgeResidency. Qualify the body postcondition.',
          'old': {'path': old.name, 'sha256': hashlib.sha256(before).hexdigest(), 'lines': 44},
          'new': {'path': new.name, 'sha256': hashlib.sha256(after).hexdigest(), 'lines': 44},
          'context_and_header_unchanged': True}
(HERE / 'drafts/source-qualification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
