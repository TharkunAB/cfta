import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-rank-resources.txt').read_text().strip()
cfg = json.loads((HERE / 'checkpoint-result.json').read_text())
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source = ROOT / 'lean/MicroCFTA/SourceCurrentOuterRankEnvelopeResources.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == cfg['source_sha256']
assert len(source.read_text().splitlines()) == cfg['source_lines'] <= 500
assert not (HERE / 'rank-resources-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert f"Build completed successfully ({cfg['audit_jobs']} jobs)" in audit
assert f"{cfg['audit_dependencies']} MicroCFTA theorems" in audit
assert {item['path'] for item in json.loads((HERE / 'components.json').read_text())} == {
    'rank-resources', 'independent-review', 'resource-plan', 'resource-plan-review'}
full = (HERE / cfg['full_relative_path']).read_bytes()
assert len(full) == cfg['full_bytes']
assert hashlib.sha256(full).hexdigest() == cfg['full_sha256']
update = f'''## Conditional resources for the finite rank envelope

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-rank-resources.md`.

OuterRankEnvelopeResources.node_call proves that a successful node call
returns a checked state within the SAME finite envelope's output profile
and guard alphabet. The literal call must be reached from the original
global root. That root supplies its stated Context, Frame, Fits, carrier,
Inputs, old ScheduleF Room, union normality, native support, causal history,
Merge stores and support, and Parent origins. The local entry supplies
Fits and carrier for its exact seed, plus Room for the envelope output.
Both resource predicates concern the checked component of the SAME
actual returned caller.
It assumes successful return. It does not establish successful return.

The 37-line public header keeps every original premise. The proof uses
induction on actual node fuel and chronological row and child-list
inductions. The selected Parent receipt bounds its returned child list
by its fixed returned profile mass. Finite retention carries each child
image through the remaining slots and rows. Raw constructors consume
states padded to the complete slot or row profile before construction.
The public envelope and its numeric stage theorem remain unchanged.
The proof adds no future resource callback or replacement envelope.
Original global ScheduleF resources stay separate from local C resources.

The selected source has {cfg['source_lines']} lines below the 500-total-line stop.
Author/root strict checks, the sole complete FULL, independent review,
and Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
There are {cfg['actual_jobs']} actual Lean/Lake commands, including {cfg['failed_jobs']} failures.
Every actual input, complete raw log, and exact repair remains archived.
Whole checked/printed type identity, all eight printer settings, public
type scope, and actual axioms pass. Default proof limits stay unchanged.
Only the old Audit warning remains. No runtime, canonical, constructed,
infrastructure, or reviewer proof job ran. Counts are not completion.

The largest execution gap is adequate OUTER fuel for the SAME actual run.
The strongest outer execution theorem remains DoneOrExhausted under its
FULL initial packet and nine lower-fuel bounds. Its run erases phase
output to Unit. This conditional resource theorem does not remove the
exhausted alternative. General envelope bounds at every execution prefix
and every intermediate Parent peak are not established here.

A source-only adequacy plan computes C and W first, then reserves the old
Schedule at W. It classifies the original root once and lifts any reached
failure to that root. It needs a strict-rank induction and the exact child
offset +3+rowIndex+slotIndex. It must prove positive walk fuel before it
uses child reachability or rank. It can use the conditional resource
theorem only after it proves the selected child returns successfully.
This plan and any later header remain unproved source assessments.

A separate manual source argument finds a fixed-width limitation:
C at numeric rank (0,1) has output nodes at least 183 for every seed.
Its Room premise therefore requires bits at least 33672. The raw rebuild
bound h(b)=b*b+b+1 gives the lower-bound sequence 1, 3, 13, 183.
The literal empty value has this rank, but its actual worker skips the
virtual work reserved by C. This is a limit of the coarse forecast.
It is not a checked Lean theorem, actual allocation count, Haskell fault,
machine-word-size claim, or termination counterexample. See the frozen
`capacity-assessment` note and its source index in this checkpoint.
Joint initial capacity, useful fixed-width feasibility, and state/cache
widening remain open. Larger mathematical widths are not ruled out.

Finite renewals, final retention, general successful completion,
convergence, broader resources and Haskell refinement remain open.
Whole-library termination is not proved. The broadest semantic result
remains exact finite-term language preservation for a supported
successful traversal with empty inherited constraints. General inherited
constraints give narrowing, with exactness under inherited satisfaction.

All earlier proofs, failures and counterexamples remain. All Haskell and
package files remain unchanged. No new Haskell defect or repair is claimed.
FINDINGS keeps its external Haskell repair index FIRST.
Work continues at the user's request.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
OuterRankEnvelopeResources.node_call now bounds the checked state at the
SAME successful node return by the original finite C output profile and
guard alphabet. It retains the original global packet, old ScheduleF
Room, exact local entry Fits/carrier, and local C-output Room.
It assumes successful return. Adequate OUTER fuel remains unproved.
The strongest outer execution statement remains DoneOrExhausted under
its full initial packet. Whole-library termination is not proved.

The {cfg['source_lines']}-line source, author/root strict, sole complete FULL,
independent review and Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
{cfg['actual_jobs']} actual commands include {cfg['failed_jobs']} failures. Complete raw evidence remains.
Default proof limits, public type identity, eight settings and actual
axioms pass. Only the old Audit warning remains. No runtime check ran.

New capacity finding, SOURCE REVIEW ONLY: for every seed and budget,
C at rank (0,1) has output nodes at least 183. Its Room condition implies
bits at least 33672. The symbolic rebuild chain is 1, 3, 13, 183.
Thus this sufficient reservation cannot hold at mathematical bits=64.
The literal empty value has rank (0,1); C reserves unused virtual work.
This concerns the coarse profile, not actual allocation or Haskell width.
It is not a Lean theorem, runtime defect, or termination counterexample.
No full genuine initial resource packet or widening construction is given.
See `lean/restart-evidence/20261021-outer-rank-resources/capacity-assessment/note.md`.
Useful fixed-width capacity and state/cache widening remain open.

No Haskell source, package, repair or runtime result changes.
Read `lean/notes-current-outer-rank-resources.md`.
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
note = '# Conditional resources for the finite rank envelope\n\n' + update
note += f"\nSelected source SHA256: {cfg['source_sha256']}.\n"
note += f"Sole FULL: {cfg['full_bytes']} bytes; SHA256 {cfg['full_sha256']}.\n"
note += f"Printer SHA256: {cfg['printer_sha256']}.\n"
note += f"Actual axioms: {cfg['axioms_summary']}.\n"
(ROOT / 'lean/notes-current-outer-rank-resources.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
