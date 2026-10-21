import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
assert json.loads((HERE / 'audit-1.json').read_text())['exit_code'] == 0
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3619 jobs).' in audit
assert '75221 MicroCFTA theorems' in audit
selected = json.loads((HERE / 'selected-sources.json').read_text())
for name, pin in selected.items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == pin['sha256']
    assert not (HERE / (pin['strict'] + '.log')).read_bytes()
    assert json.loads((HERE / (pin['full'] + '.json')).read_text())['exit_code'] == 0

update = f'''## Completed reduction return invariants

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-warm-return.md`.

SourceCurrentOuterClosedInputs.node_call proves that the SAME completed
nodeCall retains NodeStored and returns a closed result from a closed input.
It uses the original entry resources and actual done equation.
One private stronger reached lemma exposes the existing complete induction.
The original public reached signature stays byte-for-byte unchanged.
The local complete proof and original cut induction remain unchanged.

SourceCurrentOuterResourceWriters.node_call retains Origins in the SAME
final edgeResults table. It preserves each stored edge's correlated
historical Parent writer and resources. Its proof projects all_origins.
It adds no induction, import or private helper.
Both endpoints use past completion. Neither assumes a future successful
call, future Room, callback law or enclosing ancestor.

The selected sources have 479 and 489 lines. Net additions are 59 and 24.
Both original sources, exact headers, failed input and repair remain.
The closure wrapper needed two explicit Reached.refl phase arguments.
Selected strict checks are clean. One sole FULL per module verifies all
three public TYPEs, check/print identity and the actual standard axioms.
Root and independent review read every printed TYPE line.
Private helper names and dagger spellings are absent from these TYPEs.
Proof declaration limits and the existing Audit imports stay unchanged.
Audit passes: 3619 jobs /75221 theorem dependencies.
Six actual Lean/Lake commands include one failed closure check.
Only the old Audit warning remains. Copies add no proof jobs.

Existing public results already retain both idle result tables, Context,
Frame, Fits, carrier and the five native-store laws.
The two missing completed-return projections are now public.
The complete next-entry packet still needs assembly.
The next resource task is finite repeated calls through the SAME populated
caller and global stores at one width chosen before initialization.

The count/mass assessment is source-only. Its proposed pure count bound
would cover each available entry by a finite count/mass grid.
A finite join of C outputs and old schedules at each precomputed stage
could reserve several calls without C monotonicity or caller widening.
The count bound and finite-call reservation are not proved here.
Keep every stage's exact seed. Do not recompute C at the final seed.

The strongest combined execution result remains the checked cold theorem:
one source-built cold node call succeeds at sufficient mathematical width
and preserves exact finite-term language relative to the guard evaluator.
Practical fixed widths, repeated-pass composition and convergence,
solver-contract and exported-table composition, and concrete Haskell
refinement remain open. Counts do not measure whole-library completion.

All earlier proofs, counterexamples, marked drafts and optimized interned
sources remain. Older constructor and equality work remains secondary.
No Haskell source, package, repair or runtime result changes.
FINDINGS keeps the external Haskell repair index FIRST.
Work continues at the user's request.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
Completed node calls now have public NodeStored/closed-result and historical
edge-writer Origins postconditions. They concern the SAME actual return.
The old reached signature and all original induction content remain.
Two explicit Reached.refl phase arguments repair the first closure check.
Original sources, failed input, complete raw logs and exact repairs remain.
Strict checks, sole FULLs, independent TYPE review and Audit pass:
3619 jobs /75221 theorem dependencies. Six actual commands include one
failure. Only the old Audit warning remains. No new axiom is used.

The complete next-entry packet, same-width finite-call reservation and
repeated-pass composition remain open. The finite count/mass grid proposal
is source-only. Practical machine bounds and Haskell correspondence remain
open. No Haskell source, package, repair or runtime result changes.
The external Haskell repair index stays FIRST.
Read `lean/notes-current-warm-return.md`.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
index = (ROOT / 'lean/restart-evidence/20261021-cold-rank-capacity/haskell-repair-index.md').read_text()
(HERE / 'haskell-repair-index.md').write_text(index)
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
        marker += index.rstrip() + '\n\n'
        assert original.startswith(marker)
        changed = marker + findings + '\n' + original[len(marker):]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
note = '# Completed reduction return invariants\n\n' + update
for name, pin in selected.items():
    raw = (HERE / (pin['full'] + '.log')).read_bytes()
    note += f"\n{name}: source SHA256 {pin['sha256']}.\n"
    note += f"Sole FULL: {len(raw)} bytes; SHA256 {hashlib.sha256(raw).hexdigest()}.\n"
(ROOT / 'lean/notes-current-warm-return.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
