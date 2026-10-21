## Current outer execution excludes every active node-owner collision

Updated: 2026-10-21 12:42 CEST. Proof checkpoint: `841fe6e4c9`.
Start: `04983c1956`. Imported main remains `794903b3f`.
Read `lean/notes-current-older-owner-busy.md`.

OlderOwnerBusy.no_node_busy now excludes nodeMemo(handle,busy) from the
literal outer run against ANY enclosing active node ancestor. It works
from an arbitrary initial Phase with the genuine initial semantic and
resource packet, writer Origins and explicit initialNodeIdle. No node
cell may be evaluating at entry. State.initial has empty outer tables and
satisfies this boundary. Warm suspended or returned cells remain permitted.
Context alone does not imply initial idleness. No edge-idle premise is
needed for this node-only result.

Existing InitialBusy.busy derives the exact reached fault request and the
evaluating cell containing that SAME complete request. The same prefix's
owners theorem derives its actual activation and unfinished body prefix.
One body_rank_lt call then gives strict decrease from this request to
itself. Either Lex constructor contradicts Nat.lt_irrefl. The proof adds
no induction, canonical equality helper, selected-owner oracle or future
return. This closes arbitrary older-node-owner busy exclusion.

The largest remaining progress gap is a first adequate outer fuel together
with an initial resource envelope. InitialFuel.phaseNeed and forecast Room
bound a CHOSEN fuel. They do not construct a sufficient fuel. Existing
done-stability results start from a success. The current generic NodeReady
also means allocated and available, not closed: issued bare references
are available, while nodeBody rejects a bare reference. A supported-input
closure condition and its actual-prefix transport remain to be established.
This is a source contract boundary, not a constructed execution counterexample
or Haskell defect. Existing available-Mu and inherited-prefix completion
producers must be reused. Finite-ordinary completion already has a genuine
initial-resource result on its narrower Domain and quantitative profiles.

Busy exclusion does not itself bound fresh renewals or prove successful
completion. Final retention, outer completion, convergence, broader initial
resource production and Haskell refinement remain open. The broadest
semantic claim remains exact finite-term language preservation for a
supported SUCCESSFUL traversal with empty inherited constraints. General
inherited constraints give narrowing, with exactness under inherited
satisfaction. Whole-library termination and implementation refinement are
not proved.

Strict, complete FULL, independent review and Audit pass. Audit has
3610 jobs /75057 dependencies. Four actual Lean/Lake commands all pass.
The unchanged 69-line source needed no repair. Its sole public header
matches the exact approved proposal. Selected/root strict logs are empty.
Whole checked/printed type identity, all eight printer settings and actual
standard three axioms pass. No canonical, infrastructure, constructed,
runtime or reviewer proof job ran. Only the old Audit warning remains.
Counts are not completion.

All older proof/evidence bytes and version exceptions remain. Haskell,
packages, imported main, stashes and other worktrees stay unchanged.
No new Haskell defect or repair. FINDINGS keeps its external repair index
FIRST. Work continues as requested.
