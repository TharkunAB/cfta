# Fixed-reader reconstruction and actual support

Updated: 2026-10-18 12:21 CEST. Proof checkpoint is `03f0f57b`.
Starting checkpoint is `ac6fbc08`. Main source remains `c0cc8a05`.
Read `lean/notes-current-reader-support-reconstruction.md`.

Finite observation agreement now uses a reader separate from the actual
execution heap. Indexed strict ordinary-child hypotheses retain complete
row fields and ordered children. Indexed strict union-member hypotheses
quantify the execution heaps. Actual member completion and replay can
allocate missing grouped nodes while the observation reader stays fixed.
No input observation relation is transported through those effects.

Initial Ready data now constructs both raw source calls and both stored
reconstructions for an established cross-execution source case. Actual
calls, final execution heap, Keeps, availability and histories are derived.
Strict syntax induction derives the case for every BinderFree source,
with distinct finitely related recursive replacements. A separate closed
source clause permits arbitrary nested used binders with no external input
dependencies. The general varying-capture active binder clause stays open.

Generic WarmSupport is closed under epsilon successors and ordered row
children and requires actual effect-free unfolding. It derives exact row
and reference origins and finite Same comparison equivalence after growth.
A finite actual preparation now produces such support for every closed
available value at its final reader. Its well-founded unfinished-degree
vector covers newly allocated lower-degree Mu records. No BinderFree or
finite ordinary Cap condition is added to preparation. This does not prove
observation equivalence between the cold and prepared readers. Generic
support permits open values; automatic preparation covers closed values.

Checked source examples show why these distinctions are required. A warm
normalized union can have a cold original ordinary subgroup. A nested used
Mu unfolding returns an ordinary successor and a nested used Mu child that
are available only at its returned heap. Unrelated edge allocation can also
change exact physical row origins of a cold unfolding. This last example
does not refute finite Same transport. Actual preparation and later support
transport are checked on two distinct related recursive values.

The general binder proof still needs source-derived literal root matching
for the callback filters and a noncircular recursive epsilon argument.
It cannot assume its self values related at the same depth. The full
actual-source Forward instance, initial query-operand ancestry, all active
node-owner exclusions, fresh-call bounds and general recursive completion
remain open. Repeated convergence, equality-operation resources, host Int
adequacy and public Haskell correspondence remain separate obligations.
The strongest general outer language theorem assumes a supported successful
run. The full-library goal remains active.

Full Audit passes 3304 jobs and 71623 checks. Eighteen new public
heads include the two Preparation constructors. Four constructed heads
also pass full statement, proof and axiom checks. All seven selected strict
logs are empty. All four new canonical builds are warning-free. Audit
retains only the old ClosedCompletion warning. Four component manifests
pin 257 entries. Independent review finds no material issue.
Evidence is in `lean/restart-evidence/20261018-reader-support-reconstruction/`.

No Haskell patch or new executable defect is added. FINDINGS retains the
external repair registry first. Field-pool repair b9219b9e remains fixed
in c0cc8a05. Publication awaits the existing direct approval. No push is
retried.

The four production modules are SourceCurrentFiniteObservationExecution,
SourceCurrentReaderFiniteUnionStep, SourceCurrentFiniteReconstruction and
SourceCurrentObservationReaderSupport. Audit adds only these four imports.
All 30176 starting tracked files remain. All 3297 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Preservation
checks 160 frozen manifests with 1059 module entries. Earlier proofs,
repairs, counterexamples, drafts and the optimized core remain unchanged.
Selected jobs use 4GiB maximum/high limits, zero swap and five-minute caps.
Successful root jobs peak at most 358MiB. This is component evidence, not
whole-library correctness.
