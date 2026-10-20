import datetime
import json
from pathlib import Path
from zoneinfo import ZoneInfo

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
proof = (HERE / 'proof-commit.txt').read_text().strip()
stats = json.loads((HERE / 'attempt-accounting.json').read_text())
stamp = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
fixture = (HERE / 'fixture-summary.md').read_text()
block = f'''## Current generated-row full-Mu capture ancestry

Updated: {stamp}. Proof checkpoint: `{proof[:9]}`.
Verified start: `0dab9a59d`. Imported main remains `794903b3f`.
Read `lean/notes-current-native-generated-row-capture-backedge.md`.

An actual native optional execution and its generated Observed receipt
now fix one publication event and raw callback before all stored rows
and actual successful unfold anchors. Each same complete row has an
actual nonunion terminal build. Its node, binder and capture alternatives
retain Context, Reached, a syntax bound and both callback suffixes.
A capture retains its exact terminal lookup, active source Path, original
slot offset and exact leaves occurrence. A row-bearing capture is closed.

For a full-Mu capture, actual body availability supplies the same full
resident cell before this optional operation. Its key differs from the
new target key. One lower capture proof gives the same complete row an
original indexed node SourceRow/build/RowCall or an actual generated
producer at a strictly earlier native prefix. Both arms retain their
complete receipts. The initial arm fixes the same indexed original path
before all generic rows. The earlier generated arm stays unchanged.
No input-pool nonemptiness, writer identity or decreasing rank is assumed.

An actual successful unfold keeps its stored-row anchor, symbol,
constraint and arity, plus identity or actual ordered child Calls.
The new ancestry result applies to that stored anchor. Changed returned
children need not equal the stored children or original node output.

{fixture}
One public and one constructed full readback pass with standard axioms.
Selected root strict logs are empty. Canonical and default Audit pass:
3541 jobs and 74341 theorem dependency checks. Only the existing
ClosedCompletion warning remains. All {stats['capped_commands']} actual capped Lean/Lake commands
and {stats['failed_commands']} failed commands remain. One zero-exit incomplete public
printer is rejected. Successful predecessor checks remain unselected.
Counts do not measure completion. Exact large logs use verified lossless
archives. Every earlier proof, draft, repair and counterexample remains.

Generated node and non-Mu capture ancestry, warm binder reuse, self
replacement and residual observations remain open. Global owner renewal,
active-owner exclusion, final retention, general outer completion,
convergence and production Haskell refinement also remain open.
All 268 Haskell and 207 active package files keep their bytes.
FINDINGS retains the external repair registry first. No new Haskell fix
or runtime result is claimed. The full goal stays active. Pushes to
formalize remain authorized.

'''
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
         'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
         'lean/notes-current-system-claim.md']
for name in paths:
    path = ROOT / name
    text = path.read_text()
    assert '## Current generated-row full-Mu capture ancestry\n' not in text
    if name == 'NEXT-PROMPT.md':
        prefix = 'Continue the cfta formalization in /home/tritlo/Code/mcfta.\n\n'
        assert text.startswith(prefix)
        text = prefix + block + text[len(prefix):]
    else:
        first, rest = text.split('\n', 1)
        text = first + '\n\n' + block + rest.lstrip('\n')
    path.write_text(text)
finding = f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:9]}`.
Actual generated rows now keep their same terminal SourceRow and actual
build under one fixed Observed event and raw callback. An actual full-Mu
capture retains its exact original leaves slot, same stored row, current
availability and resident full cell, and distinct new-target key.
One lower capture proof gives that same row original indexed node
production or an actual strictly earlier native generated producer.
Both alternatives retain complete receipts. Actual unfold anchors keep
symbol, constraint, arity and identity or actual ordered child Calls.
The node, binder and non-Mu capture cases remain explicit.
One public and one constructed full readback pass. Selected root strict
logs are empty. Default Audit passes: 3541 jobs and 74341 dependency checks.
All {stats['capped_commands']} actual Lean/Lake commands and {stats['failed_commands']} failed commands remain.
The zero-exit incomplete public printer is rejected. Earlier successful
source checks stay unselected. Large logs retain their exact raw bytes
through verified lossless archives and unchanged component manifests.
No new Haskell fix or runtime result is claimed. The imported PR #97
repair and all earlier external fixes remain above or below this update.
Prior formatter results remain valid for unchanged source files.
All 268 Haskell and 207 active package files keep their bytes.
General generated ancestry, warm reuse, self replacement, residual Mu
observations, global renewal, active-owner exclusion, final retention,
outer completion, convergence and Haskell refinement remain open. Read
`lean/notes-current-native-generated-row-capture-backedge.md`.
Preserve every external repair, reproducer and validation result below.

'''
(HERE / 'findings-update.md').write_text(finding)
path = ROOT / 'FINDINGS.md'
text = path.read_text()
position = text.index('Current proof update:')
path.write_text(text[:position] + finding + text[position:])
path = ROOT / 'lean/notes-current-native-generated-row-capture-backedge.md'
text = path.read_text()
first, rest = text.split('\n', 1)
path.write_text(first + '\n\n' + block + rest.lstrip('\n'))
print(json.dumps({'status': 'PASS', 'current_documents_updated': len(paths) + 2}))
