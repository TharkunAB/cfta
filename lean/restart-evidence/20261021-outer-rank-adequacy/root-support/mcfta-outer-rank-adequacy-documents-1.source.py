import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-rank-adequacy.txt').read_text().strip()
cfg = json.loads((HERE / 'checkpoint-result.json').read_text())
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source = ROOT / 'lean/MicroCFTA/SourceCurrentOuterRankAdequacy.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == cfg['source_sha256']
assert len(source.read_text().splitlines()) == cfg['source_lines'] <= 650
assert not (HERE / 'rank-adequacy-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert f"Build completed successfully ({cfg['audit_jobs']} jobs)" in audit
assert f"{cfg['audit_dependencies']} MicroCFTA theorems" in audit
assert {item['path'] for item in json.loads((HERE / 'components.json').read_text())} == {
    'rank-adequacy', 'independent-review', 'adequacy-plan', 'adequacy-plan-review',
    'cold-capacity-assessment'}
full = (HERE / cfg['full_relative_path']).read_bytes()
assert len(full) == cfg['full_bytes']
assert hashlib.sha256(full).hexdigest() == cfg['full_sha256']
update = f'''## Conditional outer fuel adequacy

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-rank-adequacy.md`.

OuterRankAdequacy.initial_node_call proves successful return of the SAME
modeled outer node call from its full initial packet. It computes the
existing finite envelope C and its outer work bound W before it reserves
the old schedule at W. One joint Room premise covers both reservations.
All nine lower-fuel bounds remain explicit. The root supplies Context,
Frame, Fits, guard carrier, Inputs, union normality, native support, causal
history, Merge stores and support, Parent origins, stored and closed
inputs, and idle initial node and edge tables. These are initial facts.
The theorem does not assume successful return or a future callback.

For every outer fuel at least W, the literal nodeCall returns the SAME
result and complete final caller. Lower fuels and the initial state stay
fixed. The proof classifies the original root once. It carries each
actual failure back to that root. A strict-rank induction then excludes
exhaustion. Child fuel retains the exact +3+rowIndex+slotIndex offset.
Positive walk fuel is proved before child reachability or strict rank.
The conditional resource theorem is used only after successful child
return. It bounds the actual checked state for the next slot or row.

The selected source has {cfg['source_lines']} lines below the 650-total-line stop.
The 36-line public header retains every planned assumption, type, order,
let, and conclusion. An additive naming correction prefixes exactly 25
unused premise labels with underscores. The entire proof body is unchanged.
The original header, complete failed inputs, raw logs, and every repair
remain archived. No linter exception or proof-limit increase is used.

Author/root strict checks, the sole complete FULL, independent review,
and Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
There are {cfg['actual_jobs']} actual Lean/Lake commands, including {cfg['failed_jobs']} failures.
The author checks include one warned success before the naming correction
and one clean success after it. Selected strict logs are empty. Whole
checked/printed type identity, all eight printer settings, public type
scope, and actual standard axioms pass. Only the old Audit warning remains.
No runtime, canonical, constructed, or reviewer proof job ran.
Counts do not measure completion of the whole-library goal.

Capacity remains a substantive premise. The frozen cold-capacity source
assessment proposes construction of a genuine initial packet at a
computed width. It is not a proof or a constructed example. Warm-state
and cache widening remain open. A separate source-only argument finds
C(0,1).nodes at least 183, which requires bits at least 33672 for Room.
This is a limit of the coarse sufficient forecast. It is not a checked
Lean theorem, actual allocation count, Haskell-width claim, runtime
defect, or termination counterexample. Practical fixed-width feasibility
and bounds for every intermediate Parent peak remain open.

A complete 137-line cold-entry candidate is retained in this checkpoint's
future-cold-capacity-draft directory. Whole source and namespace-placement
review pass. The exact 25-line proposed statement remains unchanged.
No compiler or runtime job has checked that candidate. It must pass its
own ordinary check before a separate FULL or publication. It constructs
a fresh cold caller. It does not transport a populated warm caller.

The envelope remains noncomputable in Lean. This theorem supplies a finite
mathematical outer bound under its stated packet. It does not supply an
executable fuel calculator or unrestricted whole-library termination.
Finite renewals, final retention, repeated-pass convergence, broader
resources, and concrete Haskell refinement remain open.
The broadest semantic result remains exact finite-term language
preservation for a supported successful traversal with empty inherited
constraints and explicit semantic/resource assumptions. General inherited
constraints give narrowing, with exactness under inherited satisfaction.
This language uses SourceEqualityPCSGuard.holds formulas solver.
Declarative solver-contract evidence and exact finite-table readback
remain separate obligations. A source-only integration assessment in
future-cold-semantics identifies ConstructedOuterInitial.node_call as the
same-result semantic consumer at W. It proves no new corollary.
One whole-library theorem combining these results is not established.

All earlier proofs, counterexamples, marked drafts, and optimized interned
sources remain. Older constructor and equality targets remain secondary
targets. All Haskell and package files remain unchanged. No new Haskell
defect or repair is claimed. FINDINGS keeps its external Haskell repair
index FIRST. Work continues at the user's request.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
OuterRankAdequacy.initial_node_call proves successful return under the
full initial packet, joint initial capacity, and nine lower-fuel bounds.
For every outer fuel at least the finite envelope work bound W, it returns
the SAME result and complete final caller. Successful return is proved.
The public statement assumes no future successful call or resource oracle.

The {cfg['source_lines']}-line source, author/root strict, sole complete FULL,
independent review and Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
{cfg['actual_jobs']} actual commands include {cfg['failed_jobs']} failures and one warned success.
The selected strict logs are empty. The exact 25-name header correction
preserves every premise type and the complete proof body. All original
headers, failed sources, raw logs and repairs remain. Default proof limits,
all eight printer settings, whole type identity and standard axioms pass.
Only the old Audit warning remains. No Haskell runtime check ran.

A genuine initial capacity packet remains to be constructed. The frozen
cold-capacity assessment is a source-only next-step proposal. It proves
neither a packet nor warm-state transport. The earlier coarse-capacity
obstruction remains source review only. Whole-library termination,
repeated-pass convergence, semantic composition for the same execution,
and concrete Haskell correspondence remain open.

No Haskell source, package, repair or runtime result changes.
Read `lean/notes-current-outer-rank-adequacy.md`.
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
note = '# Conditional outer fuel adequacy\n\n' + update
note += f"\nSelected source SHA256: {cfg['source_sha256']}.\n"
note += f"Sole FULL: {cfg['full_bytes']} bytes; SHA256 {cfg['full_sha256']}.\n"
note += f"Printer SHA256: {cfg['printer_sha256']}.\n"
note += f"Actual axioms: {cfg['axioms_summary']}.\n"
(ROOT / 'lean/notes-current-outer-rank-adequacy.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
