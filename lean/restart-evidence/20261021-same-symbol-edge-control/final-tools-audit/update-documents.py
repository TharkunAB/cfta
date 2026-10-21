import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
assert start == 'e03b78047a647ba1f7c99ec0d4d1c16c8f188b64'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and all(c in '0123456789abcdef' for c in proof)
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
audit = (HERE / 'same-symbol-edge-audit-1.log').read_bytes()
assert hashlib.sha256(audit).hexdigest() == '4e6d8db305002d56aa075782fee1591b65490e4db1aba48bd9006a37d249de18'
assert b'Build completed successfully (3624 jobs).' in audit and b'75337 MicroCFTA theorems' in audit
assert json.loads((HERE / 'same-symbol-edge-audit-1.json').read_text())['exit_code'] == 0
source = (ROOT / 'lean/MicroCFTA/SourceCurrentSameSymbolEdgeControl.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'dbf416168635ecc34effe17891f557f31ec14df2f7cb368c52863d69a6174559'
assert (HERE / 'same-symbol-edge-strict-3.log').read_bytes() == b''
readback = json.loads((HERE / 'public-readback/same-symbol-edge-full-readback.json').read_text())
assert readback['log_sha256'] == 'e90cfe4417e4cc5fec32da1dec6cae89d9ce3b31ef6b6a32fd61a1dfc0571bb6'
checked = (HERE / 'public-readback/same-symbol-edge-miss_readback-public-type.txt').read_bytes()
assert checked == (HERE / 'public-readback/same-symbol-edge-miss_readback-printed-public-type.txt').read_bytes()
assert hashlib.sha256(checked).hexdigest() == 'a08d7f8d6b6082591a6ebdf83a77d40507f59c1227034dcd83ae933976767206'
assert len(checked.splitlines()) == 449 and len(checked) == 34826
assert checked.count(b'\n') == 448 and not checked.endswith(b'\n')
assert readback['heads'][0]['actual_standard_three_axioms']

update = f'''## Same-symbol comparison control

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-same-symbol-edge-control.md`.

SourceCurrentSameSymbolEdgeControl.miss_readback proves the provenance of
an observed successful comparison when BOTH ordered pair keys were absent.
Its state retains the complete checked native state and a separate typed
pair memo. It publishes the original pair before demand and operand order.
A reversed call publishes a second pair and retains the original handle.
Explicit return steps finish the inner cell and then the original cell.

The theorem returns an actual direct native edgeBody trace at emptyDomain
from the SAME before.checked to after.checked. The original captured cell
contains the result. A strict reversal also has a distinct reversed cell
with that same result. All earlier returned cells remain. Unrelated memo
entries and the native tables may already be populated.
Premises are structural memo validity, both missing keys and observed
completion. No semantic meet, Room or future-success premise is added.
This theorem does not produce completion or a warm-hit historical law.

The module has 334 lines and one public theorem. Strict3 passes at default
declaration limits with linter.all and a literal empty log. Sole FULL1 has
449 logical TYPE lines, 448 LF characters and no final LF. Its checked and
printed TYPE bytes match: 34826 bytes and 34814 Unicode characters.
All eight private helpers and four private markers are absent from TYPE.
Actual axioms are the standard three. FULL1 retains 6247397 raw bytes.
Root and independent review covered the complete TYPE. The 6177481-byte
body is retained and checked programmatically; no whole manual read is claimed.
Audit passes: 3624 jobs /75337 theorem dependencies.

Five actual Lean/Lake commands remain: strict1 failed with six errors and
two warnings; strict2 exited zero with one deprecation warning; strict3
is clean; FULL1 and Audit1 pass. Audit only repeats the old inputs warning.
The six proof repairs and one deprecated-lemma replacement remain as exact
deltas. Earlier drafts, the inequality correction and added documentation
remain. The stopped first FULL materializer is metadata, not a FULL run.
Root corrected its premature empty-log commentary about strict2.

The strongest combined semantic theorem remains constructed_node_calls:
any chosen finite number of actual modeled partial reductions from a
constructed covered input, with successful continuous state and exact
finite-term language under the formalized guard semantics.
The complete withoutRedundantEdges pass is not included.

The next direct-edge semantic inventory and its independent audit are
source-only. Existing receipts retain the result and complete checked
after-state. Resident-edge growth and empty_domain derive readiness for
the next original cluster pair. Current admission, completion certificates,
sequence fuel/width/WordRanges and separate pair-memo hit history remain.
The actual ruleOut scan, cluster reconstruction, recursive Mu mapping,
whole public pass, convergence, practical fixed width, external solver
composition and Haskell refinement remain open.

All old proofs, counterexamples, marked drafts and optimized code remain.
The only old Lean edit is one Audit import. All 268 Haskell files and 207
active package files remain unchanged. No Haskell repair or runtime change
is claimed. FINDINGS retains the external Haskell repair index FIRST.
Work continues.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
SameSymbolEdgeControl.miss_readback derives the exact native body trace
and original/reversed returned pair cells from an observed BOTH-miss
comparison. It retains the SAME full checked state and every earlier
returned memo cell. The pair memo is distinct from native domain caches.
It publishes the original operands before demand and ordering.
It does not produce completion, semantics or warm-hit history.

The 334-line module passes strict3, sole FULL1 and Audit: 3624 jobs /75337
dependencies. Complete checked/printed TYPE bytes match. All 449 logical
TYPE lines were reviewed. All eight private helpers and four private
markers are absent. Actual axioms are the standard three.
The five-job ledger retains failed strict1, warned strict2, clean strict3,
FULL1 and Audit1. All drafts and exact repairs remain. No metadata adds
a proof job. The first materializer stopped before any FULL command.

The strongest combined semantic theorem remains constructed_node_calls.
The next semantic bridge inventory is source-only. Current pair admission,
completion/sequence bounds, pair-memo history, ruleOut/cluster/Mu control,
whole public pass, convergence and Haskell refinement remain open.
All 268 Haskell files and 207 package files remain unchanged. No new
Haskell repair is required. The external repair index stays FIRST.
Read `lean/notes-current-same-symbol-edge-control.md`.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
    'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
    'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
index = (ROOT / 'lean/restart-evidence/20261021-warm-next-packet/haskell-repair-index.md').read_text()
(HERE / 'haskell-repair-index.md').write_text(index)
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
        marker += index.rstrip() + '\n\n'
        assert original.startswith(marker)
        changed = marker + findings + '\n' + original[len(marker):]
        assert changed.startswith(marker + findings + '\n')
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.startswith(first + '\n\n' + update)
    assert changed.replace((findings if name == 'FINDINGS.md' else update) + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
note = ROOT / 'lean/notes-current-same-symbol-edge-control.md'
assert not note.exists()
note.write_text('# Same-symbol comparison control\n\n' + update)
print('Updated nine documents and focused note. All prior text remains.')
