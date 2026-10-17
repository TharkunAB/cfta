# Current library proof status and finite result-fed query resources

This checkpoint starts at published c7949534. Proof commits are 84e353ad
and 61c48e57. Source main remains c0cc8a05, merged locally at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Specify the intended behavior first. Then prove that the current public
Haskell operation implements that specification. Support must describe
initial inputs and resources. It must not assume future success or the
required output. Documented errors and validation order are observable results.
There is no completed universal public-library theorem.

The contracts include exact distinct accepted terms per node-count size,
counts, enumeration order, both rank/unrank inverse laws, transformation
language relations, generation coverage, and sampling laws. Language equality,
inclusion, and representative restriction remain separate contracts. Terms,
accepting runs, and generator members remain separate objects.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact classes and counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. | Current host/solver adapters and full public composition. |
| Interned construction | Finite modeled repaired construction, including nested Mu and unions. Initial captures bound full stored and returned payload mass. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive intersection | Supported closed original operands construct stable semantic execution at a computable initial fuel ceiling. The proof retains Mu, references, unions, swaps, resets, rows, and edge children. | General constrained callers and public runtime correspondence. |
| Complete generated native queries | The same constructed joint receipt carries exact language, cap, origins, and computable instruction/resource bounds from its initial entry. | Resource composition with other source operations between native queries. |
| Finite result-fed programs | One initial numeric forecast constructs every supported finite indexed query program. Later queries select actual earlier results. The same returns retain readiness, inventories, native tables, equality operations, global-table validity, language, and final resource bounds. | Actual caller lowering, interposed projection/Merge work, adaptive control flow, and concrete capacity. |
| Other serial components | Earlier fixed-source query budgets and result-fed optional binders remain preserved. | General caller integration. |
| Merge and selected Operand | Memo-aware Merge produces cap certificates. Selected domains complete Operands with unrelated open ordinary siblings. | Numeric resource bounds through actual interposed Operand work and arbitrary constrained caller completion. |
| Mixed Edit and class pass | Actual reads and the tail-first class pass retain stores and finite syntax depth. | General first Target/Force misses and complete editor/class execution. |
| Ordinary constrained reduction | Initial profiles construct a complete modeled pass with guarded language and store laws. | The domain excludes Mu, references, and unions in every descendant. General descent and convergence remain open. |
| Other components | Earlier language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted-driver proofs remain preserved. | Current adapters, remaining callers, and complete public pipelines. |

A passing build, a theorem count, and finite tests do not give a completion
percentage. These results concern explicit modeled workers and caches. They
do not prove complete correspondence with compiled Haskell execution.

## Initial numeric forecast

ResourceForecast.Profile stores node, edge, domain, and payload-mass bounds
(N,E,D,S). The existing computed query bound is B = instructionBound N E S.
Let C = credit B S and M = massAfter B S. One query forecasts

`step(N,E,D,S) = (N+C, E+C, D+B, M)`.

The profile order compares all four components. Forecast step and finite
iteration are monotone. More forecast queries retain all earlier bounds.
The profile contains numbers only. It assumes no physical execution.

Room bits profile uses the existing numeric query-entry inequalities:

```
N < 2^bits
E <= 2^(bits+2)
D + 2^(N+N*N) < 2^(bits+1)
```

Room for a larger profile gives room for a smaller actual entry. Reserved
bits profile count checks the original computed forecast at each query
entry. It requires no room after the last query. For count+1 queries,
one Room check at advance profile count gives the entire reservation.
These are initial conditions, rather than assumptions about future states.
The returned D+B bound does not replace the next admission lookahead.

## The same generated-query return

CheckedJointComputedQuery.generated_complete constructs its own full joint
receipt. It derives instruction count and resource bounds directly from
that same receipt.trace. No second execution or result alignment is needed.
The causal Stored S supplies the bounds throughout.

GeneratedQueryResources.Fits bounds actual counters and Stored mass by a
profile. Frame retains physical readiness, current inventory admission,
semantic/guard context, completed joint laws, and captured origins.
Frame.initial derives the empty-native-table laws from initial readiness,
a causal guard heap, and an inventory at that source.

The complete producer derives actual entry room from Fits and Room. Its
constructed joint trace also derives full Ready, global-table validity,
physical effects, and exact intersection language. The returned Receipt
keeps the original joint receipt and the TargetQuery receipt at the same
result and full Checked state. It widens all resources to step profile by
instruction, credit, and mass monotonicity. Populated native tables and
equality operations remain in that exact returned state.

## Finite indexed query programs

A program is a finite list of pairs of natural indices. The initial pool
contains available closed values with one Cap Plain depth bound. Each query
selects two pool values and appends its literal returned result. Original
pool indices stay stable. Later indices can select any earlier result.

Supported checks each pair against the initial pool length plus the number
of preceding queries. It uses no future value property. Every actual result
derives availability, closedness, cap, original syntax, and its receipt.
The next selection pool retains all earlier values through actual growth.

GeneratedQuerySequence.complete_many constructs the full Run from Supported,
Reserved, initial Frame, Fits, Pool, and valid global tables. Every Run step
keeps both successful index reads and the complete same-return Receipt.
The final state retains Frame, Fits at the original iterated forecast,
full extension, available closed capped pool values, and the same valid
global tables. The number of results is the program length. There is no
supplied completed run, future Trace, WordRanges, later actual counter,
or desired output law.

This theorem covers finite indexed native query programs. Actual Target
folds interpose Operand projection and Merge work between their queries.
TargetComplete.fold_complete still takes FoldRanges over reached states.
The new query sequence theorem does not derive those interposed resources
or remove that premise. The source gate can accept classes with unrelated
unselected constrained Mu roots. A whole-forest cap premise does not cover
all those cases. Data-dependent caller control flow, outer descent,
convergence, and public source/runtime correspondence remain separate.

## Validation

The pinned Lean 4.34.1 Audit passes 2894 jobs and 64310 dependency checks.
All four final production strict logs are empty. Imported validation checks
39 public declarations and seven constructive integrations. All 46 complete
signature and axiom pairs pass in seven groups. Only propext,
Classical.choice, and Quot.sound occur. Read checkpoint-validation.json for
component manifests, complete signatures, and exact source/log hashes. Four
proof manifests verify 118 entries. The next-target survey adds 24 entries.
Aggregate validation checks five manifests with 142 entries.
Raw failed attempts and their source snapshots remain preserved.

Preservation retains 13268 starting files, 2889 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, stashes, and three other
worktrees. All 79 frozen manifests retain their 651 entries.

The concrete integration constructs two original row sets {a,b} and {a,c}.
Their first intersection returns singleton node 3 with row {a}. That node
is absent from the original source and full input carrier. The second call
uses that exact returned node and the retained original right operand.
One initial forecast constructs both calls. The exact intermediate state
contains populated native node and edge cells and an actual prepared valid
equality descent record. The final state explicitly retains the first returned native node and edge
cells and that same valid equality record.

The independent three-query integration constructs [(0,1),(2,0),(3,1)] from
[left,right]. It extracts all three literal receipts and proves that the
third result has exactly the language left intersection right. It also
retains the final forecast, readiness, pool, and global tables. No caller
run, completed trace, or future room premise is supplied.

## Remaining work

1. Discharge actual Target/Force range and completion assumptions from
   initial resources. Account for projection and Merge work between native
   queries. Preserve selected domains with unrelated open ordinary siblings,
   actual source call order, populated caches, and all global effects.
   Read next-constrained-survey.md in the evidence directory for the exact next target.
2. Complete mixed Edit/ClassPass and initial active/stored outer-descent
   producers. Cover arbitrary constrained Mu bodies. Preserve the source
   gate that accepts closed no-Mu endpoints independently of their own guard.
3. Prove repeated reduction convergence and remaining recursive callers.
   One finite program or complete reduction pass is not a fixed point.
4. Complete current typing/refinement and drawn-field adapters, symbolic
   measures, documented errors, validation order, and generator rank order.
   Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
5. Compose full public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines.

Logical mass is not bytes. A yielded Work or optionalBinder counts once;
its internal constructor and solver work need separate measures. The numeric
forecast is conservative and can be very large. No practical runtime or
memory-capacity claim follows. Preserve all earlier proofs, counterexamples,
repairs, and marked drafts, the optimized interned core, and the older
constructor and equality work.

## Haskell handoff

No Haskell source change or new behavior defect occurs. Root FINDINGS keeps
current repairs first. Repair b9219b9e is merged in c0cc8a05. The original
Chain example returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds
retains opaque-pool evaluation. The earlier unfixed report is explicitly
historical and retains its original evidence bytes.
Reuse the unchanged strict Nix build, 798 examples plus golden, Fourmolu,
and Cabal-gild evidence. Record each later fix in root FINDINGS with its
failure, reproducer, paths, commit, checks, and upstream status.
