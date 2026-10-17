# Current library proof status and computed native query budgets

This checkpoint starts at published 50c8132a. The proof commits are
318feeea, 20f9b603, and feedd09e. Source main remains c0cc8a05,
merged locally at 896b0a1c. The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

First specify the intended behavior. Then prove that the current public
Haskell operation implements that specification. Support must describe the
initial inputs and resources. It must not assume future success or the
required result. Documented errors and validation order are observable results.
There is no completed universal public-library theorem.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, and both rank/unrank inverse laws. They also
include transformation language relations, generation coverage, and sampling
laws. Language equality, inclusion, and representative restriction remain
separate contracts. Terms, accepting runs, and generator members remain
separate objects.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact classes and counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. | Complete current host/solver adapters and public composition. |
| Interned construction | Finite modeled repaired construction, including nested Mu and unions. Initial captures bound complete stored and returned payload mass. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive intersection semantics | Closed original source operands construct stable successful execution at a computed initial fuel ceiling. The proof retains Mu, references, unions, swaps, resets, rows, and edge children. | Full constrained callers and public runtime correspondence. |
| Complete native query resources | Initial counters, causal Stored, closed original operands, Good, SemanticReady, Idle, and numeric headroom construct their own checked physical receipt. Its exact trace, result, stores, and identity supplies satisfy a computed instruction schedule. | Initial-only resource composition across newly generated query operands and total memory capacity. |
| Current joint inventories | Existing generated-query semantics retain captured origins and support actual produced operands with populated caches. | Compose these laws with the computed physical resource producer on the same trace. |
| Original-source serial queries | One initial budget constructs finite query lists over a fixed source, with warm caches. | Queries that use new results outside that fixed inventory. |
| Generated optional binders | One initial source bound constructs result-fed optional binders and exact checked physical traces. | General complete native query sequences. |
| Merge and selected Operand | Memo-aware Merge produces cap certificates. Selected domains complete Operands with unrelated open ordinary siblings. | Arbitrary constrained Mu bodies and runtime publication. |
| Mixed Edit and class pass | Actual reads and the tail-first class pass retain stores and finite syntax depth. | General first Target and Force misses and complete editor/class execution. |
| Ordinary constrained reduction | Initial profiles construct a complete modeled pass with guarded language and store laws. | This domain excludes Mu, references, and unions in every descendant. General descent and convergence remain open. |
| Other components | Earlier language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted-driver proofs remain preserved. | Current adapters, remaining callers, and complete public pipelines. |

These results concern explicit modeled workers and caches. They do not prove
complete correspondence with compiled Haskell execution. A passing build,
a theorem count, and a finite test suite do not give a completion percentage.

## Computed semantic rank

MassInputBounds reads the actual tagged payloads. Complete Mu mass includes
the body and both probes. The module constructs the same finite source input
interface as InputExact. With N initial node identities, its literal input
inventory has K = 1 + 4*N entries. The ordered pair inventory has P = K*K
entries. Duplicate occurrences remain counted.

NumericRank encodes the full termination tuple as a natural number. The
fields are the combined closed-root mass, unseen source pairs, local work
weight, and swap flag. A reset can restore all lower fields because it
strictly decreases the root field. The uniform payload mass bound S also
bounds local work. Every rank is less than

`H(N,S) = (2*S+1)*(P+1)*(2*S+2)*2`.

NumericFuel reconstructs execution by strong induction on that number.
It derives stable exact success for all fuel at least rank plus one. The
primary theorem takes no completed execution or Completes premise. Its
least-fuel corollary uses Completes only to name the existing minimum.
ComputedFuel constructs stable source execution at H from initial source
facts and Stored S. No desired result or future trace is supplied.

An invalid unissued reference tag has bounded unit fallback mass. That numeric
fact does not make the reference Available. Keys, guards, free metadata, and
cached depth are not counted as payload mass. Those exclusions do not remove
Mu bodies or child occurrences from the semantic source family.

## Computed native instructions and resources

Let E be the initial edge identity count. NumericSourceProfile proves rows
and members are at most N*S, and arity is at most E*S. Thus

`L(N,E,S) = max 1 (max ((N*S)*(N*S)) (max (N*S) (E*S)))`.

The existing instruction recurrence is `T 0 = 0` and
`T (h+1) = 4 + L*T h`. NativeComputedBudget uses `T H(N,S)` as its
instructionBound. This is a computable natural expression in N, E, and S.
It bounds the older mathematical nodeBudget. No completed physical trace
is used to choose it.

The initial producer constructs its own physical receipt. Idle permits
populated completed native tables. The receipt retains the exact native
and equality-operation state. The proof then derives widths and resources
on that same trace from the supplied causal Stored S. It does not substitute
a newly summed initialBound for S. This matters for later query composition:
a source can have Stored 3 while its summed initialBound is 5.

The result includes exact checked execute at instructionBound plus one,
returned Idle, Stored at massAfter instructionBound S, returned payload mass,
node and edge allocation credit, and domain allocation at most the instruction
bound. Future Trace, WordRanges, later counters, instruction count, and a
required output law are absent from the initial premises.

The exported receipt states physical and resource properties. Existing
contextual language laws still need composition on the same actual trace.
One Work or optionalBinder counts as one yielded instruction. Internal
constructor execution, solver work, bytes, and total memory capacity need
separate measures. Observing final pure done uses one extra execute unit.
The numeric bounds are conservative. The theorem does not claim practical
computation of the very large schedule.

## Remaining work

1. Compose complete queries that consume their actual preceding results.
   Use the current joint-inventory and contextual producers. From forecast
   (N,E,D,S), let B = instructionBound N E S. Forecast the next entry as
   (N+credit B S, E+credit B S, D+B, massAfter B S). Derive each later bound
   from the original forecast and call count. Preserve populated native,
   equality, and global caches. Admission still needs numeric room at every
   forecast entry. D+B bounds returned domains; it does not replace the next
   query's independent admission lookahead.
2. Complete general Target and Force misses, mixed Edit, and ClassPass from
   initial resources. Produce active and stored outer-descent certificates.
   Cover arbitrary constrained Mu bodies. Preserve the source gate that
   accepts closed no-Mu endpoints independently of their own guard.
3. Prove repeated reduction convergence and the remaining recursive callers.
   One complete pass is not a fixed point.
4. Complete current typing and refinement adapters, drawn fields, symbolic
   measures, documented errors, validation order, and generator rank order.
   Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
5. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

Preserve all earlier proofs, counterexamples, repairs, and marked drafts.
Keep the optimized interned core and the older constructor and equality work.
Do not repeat the completed mass, width, instruction-credit, rank, source-rebase,
origin, Merge, selected-Operand, or serial optional-binder results.

## Validation and Haskell handoff

The pinned Lean 4.34.1 Audit passes 2890 jobs and 64246 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All six final strict
production logs are empty. Imported validation checks 39 public signatures
and eleven constructive integrations. All 50 full signature and axiom pairs
pass in ten groups. Read checkpoint-validation.json for complete signatures,
component manifests, hashes, and the exact retained logs. Five proof component
manifests verify 138 entries. The source survey adds 24 entries. Aggregate
validation checks six manifests with 162 entries. Raw failed attempts
and their source snapshots remain in the evidence directory.

Preservation retains 13113 starting files, 2883 older non-Audit production
proofs, all 239 Haskell files, all 206 active-package files, stashes, and three
other worktrees. All 78 frozen manifests retain their 647 entries.

No Haskell source change or new behavior defect occurs in this increment.
Root FINDINGS keeps the repair registry first. Field-pool repair b9219b9e
is merged at c0cc8a05. The original Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque-pool
evaluation. The older unfixed report is now explicitly historical. Its
original bytes remain in this checkpoint's evidence and Git history.
Reuse the unchanged strict Nix build, 798 examples plus golden, Fourmolu,
and Cabal-gild evidence. Record later Haskell repairs with their failure,
reproducer, paths, commit, checks, and upstream status in root FINDINGS.
