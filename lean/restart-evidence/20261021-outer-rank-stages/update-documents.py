import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-rank-stages.txt').read_text().strip()
cfg = json.loads((HERE / 'checkpoint-result.json').read_text())
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source = ROOT / 'lean/MicroCFTA/SourceCurrentOuterRankEnvelopeStages.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == cfg['source_sha256']
assert len(source.read_text().splitlines()) == cfg['source_lines'] <= 250
assert not (HERE / 'rank-stages-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert f"Build completed successfully ({cfg['audit_jobs']} jobs)" in audit
assert f"{cfg['audit_dependencies']} MicroCFTA theorems" in audit
assert {item['path'] for item in json.loads((HERE / 'components.json').read_text())} == {
    'rank-stages', 'independent-review', 'stage-plan', 'stage-plan-review'}
full = (HERE / cfg['full_relative_path']).read_bytes()
assert len(full) == cfg['full_bytes']
assert hashlib.sha256(full).hexdigest() == cfg['full_sha256']
update = f'''## Current numeric bounds for every finite envelope stage

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-rank-stages.md`.

OuterRankEnvelopeStages.stage_bounds proves the original all-stage numeric
statement for the SAME checked finite envelope. It adds no premise.
The 34-line public header keeps each literal row and slot prefix. It
bounds the selected Parent fuel, Parent seed, every slot prefix, and every
allowed child envelope by the total result. Bounds include work, lower
fuel, all profile fields, and the raw guard alphabet.
The child work bound keeps the exact +3+rowIndex+slotIndex offset.
The complete slot prefix is included. Child selection requires a strict
slot bound. The row's post-Parent mass fixes the slot limit throughout.

The separate module imports the original concrete envelope. That original
definition and its entry-retention theorem stay unchanged. The new proof
unfolds one public envelope layer and proves finite fold bounds. It adds
no replacement envelope, imported private-name call, recursive output law,
seed-monotonicity premise, physical-state oracle, or completion callback.
The calculation remains noncomputable in Lean. No runtime evaluation ran.

The selected source has {cfg['source_lines']} lines below the 250-total-line stop.
Author and root strict checks, sole complete FULL, independent review,
and Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
There are {cfg['actual_jobs']} actual Lean/Lake commands and {cfg['failed_jobs']} failed commands.
All actual inputs, complete raw logs, and exact repairs remain in the
checkpoint. Whole checked/printed type identity, all eight printer
settings, no private names in the public type, and actual axioms pass.
Only the old Audit warning remains. No canonical, infrastructure,
constructed, runtime, or reviewer proof job ran. Counts are not completion.

The first four strict checks failed. Their exact inputs and full raw
logs remain. Repairs use core conversion syntax, one explicit fold
successor equation, correct let introductions, a general local eta proof,
and an arbitrary-accumulator Parent fuel lemma. The next repair gives
the attachment map its exact function and factors the finite proof into
a private lemma and a short public proof. Its 47 moved proof lines keep
exact bytes. Final type annotations align the same arithmetic terms.
Per-declaration proof limits stay unchanged. The original 200-line draft
and uncompiled 212-line separator draft remain. The 256-line diagnostic
printer contains the unchanged 242-line module plus 14 printing commands.

The largest gap remains sufficient OUTER fuel with noncircular INITIAL
capacity for the SAME actual run. Numeric stage coverage is now checked.
Physical correspondence and fuel adequacy are not. The strongest outer
execution result remains DoneOrExhausted under its FULL stated initial
packet and nine lower-fuel bounds. The actual run erases phase output
to Unit. This numeric result does not strengthen that execution claim yet.

The source-only physical inventory identifies the next resource bridge:
actual row-entry Fits and carrier for the EXACT envelope row-prefix seed.
The existing Parent receipt then bounds every unchanged child input and
the child-list width by the fixed post-Parent mass. Literal slot retention
can carry that mass bound to the current numeric seed. A fresh physical
mass invariant at every slot is not needed for membership alone.
Completed-child and completed-row state resources still need proofs.

Keep original ScheduleF Prefix resources separate from envelope resources.
The old global prefix can supply Context, support and strict child rank
under its genuine root Room. It does not identify its seed with the new
numeric accumulator. Do not assume whole-schedule domination, child Prefix
Room, a future success, or a per-future reservation callback.
Use genuine cache readiness and coherent heap laws to identify a captured
owner with the selected request; node-key equality alone is insufficient.

Joint initial Room, actual intermediate Parent peaks, all actual nested
lower fuels, fixed-width feasibility and state widening remain open.
Finite renewals, final retention, successful completion, convergence,
broader resources and Haskell refinement also remain open. Whole-library
termination is not proved. The broadest semantic result remains exact
finite-term language preservation for a supported successful traversal
with empty inherited constraints. General inherited constraints give
narrowing, with exactness under inherited satisfaction.

All earlier proofs, failures and counterexamples remain. Haskell, packages,
imported main, stashes and other worktrees stay unchanged. No new Haskell
defect or repair. FINDINGS keeps its external repair index FIRST.
Work continues at the user's request.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
The original numeric stage-bounds statement now passes for the SAME
checked finite envelope. The exact 34-line public type adds no premise.
It covers every literal row, Parent fuel and seed, slot prefix, and
allowed candidate child. All four numeric coordinates are covered:
work, lower fuel, profile and guard alphabet. The selected-child work
offset remains +3+rowIndex+slotIndex. No replacement envelope is defined.

The selected {cfg['source_lines']}-line source, author/root strict, sole complete FULL,
independent review and Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
{cfg['actual_jobs']} actual commands retain {cfg['failed_jobs']} failed commands and complete raw evidence.
Whole type identity, eight settings and actual axioms pass. Only the old
Audit warning remains. No runtime, canonical, infrastructure, constructed
or reviewer proof job ran. Counts are not completion.

Actual-state correspondence, same-global-root capacity and adequate
OUTER fuel remain unproved. The strongest outer execution result remains
done-or-exhausted under its full packet. The next source-only inventory
isolates actual row-entry Fits/carrier for the exact envelope seed.
A Parent receipt then bounds all literal child inputs by its fixed mass;
numeric slot retention can transport that mass bound. Completed-return
resource bounds and all actual peaks still need proof.
No Haskell source, package, repair or runtime result changes.
Read `lean/notes-current-outer-rank-stages.md`.
The external Haskell repair index stays FIRST.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
        marker += (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n'
        assert original.startswith(marker + '\n')
        changed = marker + '\n' + findings + '\n' + original[len(marker) + 1:]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
note = '# Numeric bounds for finite envelope stages\n\n' + update
note += f"\nSelected source SHA256: {cfg['source_sha256']}.\n"
note += f"Sole FULL: {cfg['full_bytes']} bytes; SHA256 {cfg['full_sha256']}.\n"
note += f"Printer SHA256: {cfg['printer_sha256']}.\n"
note += f"Actual axioms: {cfg['axioms_summary']}.\n"
(ROOT / 'lean/notes-current-outer-rank-stages.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
