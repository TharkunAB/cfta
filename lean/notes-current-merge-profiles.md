# Actual recursive Merge profiles and finite callers

Updated: 2026-10-16. Audited main is `c0cc8a05`, merged at `896b0a1c`.
This checkpoint starts at published `b3df5b08`. Proof commits are
`56e098f9` and `a6756768`. Root FINDINGS keeps the Haskell handoff first.

## Full objective and current progress

Prove correspondence between the intended constrained-tree languages and
generators and the current Haskell library. Each public operation must
satisfy its contract on its stated domain. Finite operations must construct
terminating executions. Keep solver, callback, codec, machine, and host
assumptions explicit. There is no completed whole-library theorem.

Retain separate language, transformation, exact size, count, enumeration
order, both rank inverses, generator multiplicity, and probability contracts.
Exact ranks use the original sorted explicit graph rows. The optimized
interned core and older constructor/equality targets remain unchanged.
Read notes-current-caller-profiles.md for the wider proof map. Its former
general Merge profile producer gap is closed by this checkpoint.

## Universal profiles from actual calls

MergeProfileCode.Contract combines the existing physical request contract
with MergeProfileCache.Certificate. The latter quantifies over every input
row, arity, and height limit. It derives the height-indexed result envelope
and a result height no greater than the captured original input height.
The completed profile table relates each result to its own stored original.

The Code certificate strengthens old physical certificates. It retains
ordered All₂ input/result relations through each actual intermediate heap.
Actual constructor helpers derive profiles and heights for misses and
coherent cache hits. They derive closedness from residency and ordinary
profiles. They need no independent all-input closedness premise.

MergeProfileBody checks every actual source branch. Small rows retain their
original full guard and ordered child count. Large groups select original
columns, bound their multiplicity, and union their retained children.
The recursive union can need R*R rows. Its lower height permits embedding
that recursive result in the parent envelope. Group counts and exact list
relations bound the final flattened rows before actual normalized node Work.
The body certificate assumes no completed body or returned result profile.

MergeProfileProducer uses mutual induction on actual Run and Call graphs.
A hit uses physical reference injectivity and its captured owner's stored
certificate. A miss applies the smaller actual body Run induction hypothesis
to the lifted old physical certificate. This derives actual effects, the
candidate's physical contract, and both returned table invariants.

The same smaller body Run then proves the candidate's universal certificate.
Introduce arbitrary input profile limits and apply the fixed-profile body
certificate. The actual result and heap stay fixed. Height monotonicity
extends the profile to the supplied ceiling. This is a proof over the actual
recursive body. It is not an arbitrary recursive-result callback premise.

Completion retains and rereads the current table. A recursive body can have
inserted an earlier winner at the same key. The proof certifies that winner
through the returned storage invariant. It does not assign the losing
candidate's certificate to another result. Both tables remain valid.

Certificate has no profile conclusion for unsupported Mu, reference, or
explicit union inputs. Its universal implication is vacuous there. Finite
ordinary endpoints require an actual NodeShape input, so their returned
profile and height conclusions are substantive.

## Constructed finite and literal endpoints

MergeProfileFinite.allocated erases the actual allocated graph while
retaining its exact heap, output, and completed table. It returns the full
allocated physical effects and the produced certificate at that same state.

Its finite endpoint constructs its own allocated call from initial readiness,
physical storage, profile storage, and available profiled input. It derives
a stable literal worker return, both final storage invariants, output
availability, result profile, and relative height. The cold endpoint derives
the initial invariants from empty tables. No execution or returned profile
is supplied as an initial premise.

caller_finite constructs the existing full literal caller return. It then
verifies that same literal return with the new producer. It retains the
existing Post, warm surrounding caller state, completed merge table, and
language inclusion. Merge is an over-approximation. Inclusion does not
become language equality.

Imported kernels derive the next native query's computed budget from the
generated Merge profile and original input limits. They construct a second
Merge call using the first returned tables, readiness, profile, and height.
They also replay the constructed completed owner at work fuel one and any
selection fuel with identical output, whole heap, and table. These kernels
do not derive initial headroom for the Merge calls themselves.

MergeSelection proves that ordinary columns contain no recursive cover
candidates. At every comparison fuel, including zero, selection returns
distinct original inputs at the unchanged entire heap. Imported kernels
compose this fact with a literal duplicate-column graph and an empty
constructor trace. Neither supply counter changes during ordinary selection.

## Remaining work

Next prove constructor request and reservation bounds for all actual Merge
body Work and nested calls. Read next-merge-reservations.md in this evidence
directory. Its proposed recurrences are a proof plan, not proved APIs.
Then compose Operand, Target's rotated right fold, edits, class passes,
local and parent calls, and outer cumulative budgets. The ordinary root's
numeric capacity plan remains an explicit premise.

General recursive progress, repeated-pass convergence, current frontend
adapters, concrete Haskell execution, and full-pipeline composition remain
open. The graph is a completed sequential projection. Early lazy publication,
pending ancestors, concrete HashMap iteration, host interleavings, concurrent
losing candidates, and GHC forcing need separate correspondence. Equality,
sidecar, domain, and thunk resources and signed counters remain separate.

## Validation and Haskell handoff

Pinned Lean 4.34.1 passes the full Audit: 2587 jobs and 60115 dependency
checks. All 23 declared public axiom/full-signature pairs and 18 integration
pairs pass. Only propext, Classical.choice, and Quot.sound occur. Final
probes have no diagnostics or placeholders. The canonical build retains the
older unused-input warning. Initial failed drafts and logs retain their bytes.

Preservation retains 7144 starting files and 2581 older non-Audit sources.
Forty-three frozen manifests check 344 module entries. Only seven restart
authorities and two additive Audit imports may change among older files.
All older Haskell files, repairs, counterexamples, drafts, stashes, other
worktrees, and the optimized interned core remain unchanged. Evidence is in
lean/restart-evidence/20261016-constrained-merge-profile-producer/.

No Haskell changes or new verified Haskell defect. The recursive field-pool
repair b9219b9e is merged by PR #65. Root FINDINGS records its failure,
reproducer, affected paths, commit, checks, and upstream status first.
Reuse unchanged strict Nix validation, 798 examples plus golden, six-file
Fourmolu, and four-package Cabal-gild and metadata checks. The full-library
goal remains active.
