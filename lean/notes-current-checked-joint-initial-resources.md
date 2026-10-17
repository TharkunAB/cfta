# Current library proof status and checked joint initial resources

Checked at proof commit eecce203. This checkpoint starts at published 0ea50f68.
The proof commits are a041f192, c1156f5e, 22fb0df2, and eecce203.
Source main remains c0cc8a05, merged locally at 896b0a1c.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target theorems. The complete implementation theorem
does not exist yet. Support must describe initial inputs and explicit
resources. It must not assume future successful execution or the desired
result. Documented errors and validation order are observable results.

The contracts include exact distinct accepted terms per node-count size,
counts, enumeration order, both rank/unrank inverses, transformation language
relations, generation coverage, and sampling laws. Distinct terms, accepting
runs, and generated members remain separate. Exact transformations require
language equality. Over-approximations require inclusion. Representative
selection has its own restriction contract.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact size classes, counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. Validated graph keys supply a finite carrier. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired closed construction, including Mu and unions. Actual source execution produces exact guard observations and causal body/probe equality. | Concrete lazy publication, interning, and runtime correspondence. |
| Checked recursive intersection | Full checked trace induction derives cap, ranked occurrence, scope, context, and exact owner-cell laws. Existing initial numeric completion constructs the same cold return with these laws and exact language. Same-source warm calls also construct their return. | Source rebasing for newly produced operands, cumulative later-query budgets, and integration into full outer callers. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Mixed outer tables | Plain whole nodes and descendant walks construct finite execution in certified tables with other constrained owners. | General constrained node completion and initial production of active and stored certificates. |
| Rich editor and successive classes | Actual executions retain causal stores, original signed masks, caps, and physical/language receipts. Required execution constructs its finite return. | Current closed captured hereditary-leaf support is smaller than the source gate. General class existence remains open. |
| Other components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

These proofs execute literal modeled source workers and caches. The complete
correspondence with the compiled Haskell runtime is still open. A count of
theorems or successful checks does not give a completion percentage.

## Full checked joint trace

CheckedJointCode defines conditional NodeLaw and EdgeLaw for the exact
original request. Each law quantifies over every supported finite cap.
NodeLaw retains the cap, immutable-source occurrence classifier, and incoming
reference scope. EdgeLaw retains the row cap, literal child budget, and scope.
BodyCode excludes completion frames when certificates are combined over a
possibly empty set of input proofs. A local certificate does not assert
that execution exists.

CheckedJointCache retains these laws only at returned cells. Lookup and
demand preserve earlier laws. An actual finish installs the derived law
at its exact evaluating owner. Physical key safety identifies that complete
owner request at a warm hit. CheckedJointTransition retains the actual
machine and equality operations through direct, ready, and evaluating cases.

CheckedJointEdge follows the actual field loads, arity checks, equality
allocation, and rejection. Its accepted continuation walks the original
ordered children. Rejected and mismatched paths retain the sentinel and
empty-field allocation. The proof retains the same equality-operation
cache. It does not replace checked rejection with a fixed conjunction.

CheckedJointCompile certifies every selected node branch. Mu entry retains
the actual source bindings. The smaller node's universal law supplies the
ranked body result and its scope. At rank zero, the same result law at cap
zero derives annotation. At positive rank, actual probes and GuardHeap
identify the final selected constructor record and its cap. Reference reads,
ordinary rows, reset, swap, self, repeated pairs, and both unions retain their
literal behavior.

CheckedJointControl derives the next Context from each actual yielded step.
CheckedJointInduction splits the same physical trace at actual body returns.
The protected-prefix theorem identifies the running owner before finish.
CheckedJointTrace.completed discharges the full trace induction. It derives
the smaller body's universal law before publication. It has no future finish
law or desired returned-cell law as a premise. Its physical trace premise
contains the checks at reached instructions. A separate finite endpoint
constructs that trace from initial data.

## Initial resources and finite endpoints

The existing RecursiveInitialRanges theorem already derives checked request
word bounds from initial counters. For source node counter N and bits b, its
explicit bounds are N < 2^b, source edges.next <= 2^(b+2), and

`domains.next + 2^(N + N*N) < 2^(b+1)`.

The native width is b+2. The finite domain inventory supplies the exponential
term. This conservative bound can require a large width. A mathematical
width parameter is not a completed host-word adapter or a practical capacity
bound for arbitrary production inputs.

CheckedJointClosed.cold_complete combines this existing numeric completion
with the new trace proof. Initial data include Good, SemanticReady,
GuardHeap, original available closed operands, their caps, and these numeric
bounds. The theorem constructs its own contextual receipt and exact physical
trace. It retains exact intersection language, scoped and idle caches,
closedness, the returned joint Context and cell store, cap, classifier,
Original, ProbeFree, and the actual Current allocation history. It takes no
WordRanges, supplied execution, callback result law, or desired output law.

RecursiveWarmInitialRanges derives the full word and domain-prefix checks
at an arbitrary Good warm query entry from that entry's counters. It keeps
both native tables and equality operations. It requires no idle state or
completed execution to derive those range predicates.

CheckedJointWarm.warm_complete constructs finite calls for operands from
the same immutable original source. Its initial past invariants are Current,
Context, the joint and contextual cell stores, and idle native tables. Its
numeric bounds use the warm entry heap and domain counters. It retains the
actual contextual receipt and full joint return. It does not assume a future
return. It does not rebase stored laws to a different source heap or derive
all later entry bounds from a previous cold query's initial limits.

Independent mixed integration derives both Cap1 input proofs for a literal
nonhereditary ordinary node and a hereditary Mu with an ordinary body.
It proves that compileNode selects compileMu. Initial source readiness,
GuardHeap, operand residency, and numeric resources remain explicit.
The cold theorem constructs the query's own return. That same physical trace
derives its exact published cell and a two-step warm repeat. The repeat
preserves the entire checked state and uses the produced cell law. This
exact repeat needs no later-query headroom assumption. The kernel does not
construct the initial source heap from empty.

The generic native worker retains its separate WordRanges premise. No
unproved prefix transfer from checked equality code to generic code is used.
The current checked initial endpoint does not need that generic transfer.

## Remaining work

1. Rebase source-indexed native laws for newly produced operands and later
   query sources. Retain actual original-request provenance and immutable
   numeric identities. Derive cumulative allocation bounds for serial calls.
2. Use the checked joint result in finite full Target, Leaf, editor, and
   class callers. Produce their local input caps, occurrence bounds, actual
   owners, and stores from initial callers and past execution.
3. Prove general constrained recursive descent. Keep the full source gate,
   including nonhereditary ordinary endpoints. The closed captured
   hereditary-leaf family is still an intermediate supported family.
4. Prove repeated reduction convergence. Complete recursive pruning and
   compilation callers. One pass does not establish a fixed point.
5. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete solver, runtime, IO, randomness, capacity, and
   user-code adapters with explicit assumptions.
6. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

The complete library goal stays active. Do not repeat the now-proved full
checked trace induction or initial numeric cold composition.

## Validation and Haskell handoff

The full pinned Audit passes 2827 jobs and 63006 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All eleven new
production sources pass strict checks without diagnostics. All 85 imported
axiom/full-signature pairs pass in 16 groups. Ten component manifests verify
157 entries. Failed sources, raw logs, and metadata corrections remain in
restart-evidence/20261017-native-initial-resources/.
Read checkpoint-validation.json for exact hashes and groups. Canonical replay
retains only the older unused-input warning.

Preservation retains 11605 starting files, 2815 older non-Audit production
proofs, all 239 Haskell files, and 69 frozen production manifests with 584
entries. Stashes and three other worktrees remain unchanged. Preserve the
optimized interned core, older constructor and equality work, and every
earlier proof, counterexample, repair, and marked draft.

No Haskell change or new Haskell defect occurs. Root FINDINGS keeps the
external repair registry first. Recursive field-pool repair b9219b9e is
merged in c0cc8a05 and locally validated. The Chain example returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque-pool
evaluation. Reuse unchanged strict Nix all-component build, 798 examples
plus golden, Fourmolu, and Cabal-gild evidence for this source.
