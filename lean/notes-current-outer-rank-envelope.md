# Finite rank-envelope calculation and entry retention

## Current finite rank envelope and entry retention

Updated: 2026-10-21 15:39 CEST. Proof checkpoint: `ccaa8719d3`.
Start: `d44f7a36c0`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-rank-envelope.md`.

OuterRankEnvelope.envelope now defines a finite numeric prediction from
budget, count, mass, raw guard alphabet and numeric profile. It returns
work W, a lower-fuel maximum L, and an output alphabet/profile.
It uses strict Lex(count,mass) recursion with the seed as a further input.
Each slot evaluates every bounded smaller rank at THAT current seed.
It joins candidate outputs, then passes the joined seed to the next slot.
Each row starts with the existing Parent forecast and fixes its returned
mass as the slot count. Original mass bounds the number of numeric rows.
The row and final body use the existing raw-constructor forecast.
The function is noncomputable in Lean. No runtime evaluation is claimed.

OuterRankEnvelope.retains proves only mass+1 <= W and retention of the
ENTRY profile and alphabet. It has no physical or completion premise.
The concrete recurrence is internal; callers supply no recursive callback.
The exact eight-line public type has one definition and one theorem.
The selected source has 157 lines, below the 250-total-line stop.

The original all-stage theorem remains UNPROVED. This first result does
not prove child-work offsets, candidate-output coverage, intermediate
Parent peaks, or the lower maximum at all numeric stages. It also does
not prove correspondence with actual states or adequate outer fuel.
The preserved 42-line original proposal and exact equations specify that
next target. They are unelaborated source evidence, not a compiled API.
The original 215-265 estimate did not support its claimed 250 upper target.
The corrected two-head scope, original bytes and separate correction remain.

Selected author strict4 and root strict have empty logs. The sole complete
FULL covers BOTH declarations. Whole type identity, all eight settings,
no private names in either public type, and actual per-head axioms pass.
Audit passes: 3616 jobs /75112 dependencies.
There are 7 actual Lean/Lake commands and 3 failed commands.
The three failed strict checks and complete raw diagnostics remain.
Strict1 exposed a decider, pair eta, and a normalization timeout. The next
two checks retained the timeout. Strict4 names the ACTUAL Parent seed,
keeps its defining equality and rewrites the real retention fact with it.
This prevents deep forecast normalization. The strict proof budget did not
increase. All actual selected checks have no new warning. The old Audit
warning remains. No canonical, infrastructure, constructed, runtime or
reviewer proof job ran. Counts are not completion.

The strongest outer execution result remains DoneOrExhausted: the actual
formalized outer run returns normally or fails only with outer-fuel
exhaustion under its FULL stated initial packet and nine lower-fuel bounds.
That run erases successful output to Unit. The new pure calculation does
not strengthen this execution result yet.

The largest execution gap remains sufficient OUTER fuel jointly with
noncircular INITIAL capacity for the SAME run. A concrete numeric work
value now exists. Its adequacy remains unproved. Next prove all numeric
stage laws, then connect them to actual reached cuts under ONE original
initial packet. Retain current mass bounds after earlier sibling growth.
Cover all intermediate Parent profiles and all nested lower fuels.
Prove root-schedule domination or reserve an initial finite join and prove
its coverage. Do not assume future success or a per-future Room callback.
A child Prefix restart still needs extra unproved child-schedule Room.
Fixed-width feasibility and state widening remain separate open issues.
Existing request-coherence laws can relate a selected request to its
captured owner; key equality alone does not state full request equality.

Finite renewals, final retention, successful completion, convergence,
broader resources and Haskell refinement remain open. Whole-library
termination is not proved. The broadest semantic result remains exact
finite-term language preservation for a supported successful traversal
with empty inherited constraints. General inherited constraints give
narrowing, with exactness under inherited satisfaction.

All earlier proofs, failures and counterexamples remain. Haskell, packages,
imported main, stashes and other worktrees stay unchanged. No new Haskell
defect or repair. FINDINGS keeps its external repair index FIRST.
Work continues at the user's request.

Selected source SHA256: b8401732ae63be4d2036ccd4af7997b787ced8787789a1fb9d2e354047fde5ba.
The sole complete two-declaration print has 24683 bytes,
SHA256 c6426bcb61ef32b6ddb04ac59f58e202adca9a8787c9e20ba30f2b05a50ac9bf.
Printer SHA256: 7d98436155d9fed409ee26d555e4c4c7075059fd41d96f82e98748f178d08f0a.
Actual per-head axioms: envelope and retains each use propext, Classical.choice and Quot.sound.
Root independently ran the hardened full-print reader and read the complete
checked type for BOTH public declarations. No additional print ran.

The first failed source has146 lines; the first repair has156 lines.
The controlled-unfold source has157 lines, and the final successful source
also has157 lines with a different hash. All four ACTUAL strict inputs and
complete logs remain. The original147-line namespace draft and exact
prelaunch qualification patch also remain. No source exceeded the250stop.
The original source-only plan and independent review remain immutable.
They correctly retain their historical unimplemented status. This proof
package supplies a separate actual compiled status.
