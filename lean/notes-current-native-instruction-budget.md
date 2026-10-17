# Current library proof status and initial native instruction budgets

This checkpoint starts at published 59884b14. Proof commits are 1580eb22,
d2b7ca41, and d224177b. Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Support must describe initial inputs and resources. It must not assume future
success or the desired result. Documented errors and validation order are
observable results. The contracts include exact distinct terms per node-count
size, counts, enumeration order, rank/unrank inverses, transformation language
relations, generation coverage, and sampling laws. Preserve the distinctions
between language equality, inclusion, and representative restriction.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact classes, counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. | Host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired construction with nested Mu and unions. Initial syntax and captures bound complete stored and returned payload mass. | Haskell forcing, lazy publication, and runtime correspondence. |
| Checked recursive intersection | Finite exact queries on established source domains. Current joint inventories retain captured origins for produced operands. | One initial resource forecast for general result-fed query sequences. |
| Original-source serial queries | One initial numeric budget constructs finite lists over a fixed source with warm caches. | New operands outside that source and total memory capacity. |
| Generated optional binders | One initial source bound constructs result-fed optional binders and exact checked physical traces. | Other complete native query sequences. |
| Native query instructions | Initial source branching and semantic rank bound every physically checked prefix. All compiler branches and both protected finish frames retain credit. | A computed syntax-only semantic rank bound and general result-fed composition. |
| Complete native query resources | Closed original roots, initial headroom, physical semantic readiness, and idle warm tables construct their own trace. That same trace, result, store, and identity supplies fit initial budgets. | Resource bounds across newly generated query operands, concrete capacity, and public Haskell runtime correspondence. |
| Merge and selected Operand | Actual memo-aware Merge produces universal cap certificates. Selected domains complete Operands with unrelated open ordinary siblings. | Arbitrary constrained Mu bodies and runtime publication. |
| Mixed Edit and class pass | Actual reads and the tail-first class pass retain stores and finite syntax depth. | General first Target and Force misses and editor/class completion. |
| Ordinary constrained reduction | Initial profiles produce a Plan. A complete modeled pass retains guarded language and stores. | The domain excludes Mu, references, and unions in every descendant. |
| Other components | Existing language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted driver proofs remain preserved. | General descent, convergence, current adapters, and complete public pipelines. |

These results concern explicit modeled workers and caches. They do not prove
full correspondence with compiled Haskell execution. Theorem counts and
successful builds do not give a completion percentage.

## Initial instruction credit

InstructionProfile computes a fixed source branching limit L from literal
row pairs, union members, and child zips. It reserves at least one branch.
Its recurrence is `T 0 = 0` and `T (h+1) = 4 + L*T h`.

InstructionCredit assigns whole requests their initial semantic rank credit.
Bind adds continuation credit. Ordered walks retain each original occurrence.
Work, enter, read, optionalBinder, and each finish consume one instruction.
The certificate accepts actual physical returns after valid source growth.
It does not assume a completed recursive result or later instruction count.

CompileInstructionCredit derives body credit for all fourteen node dispatcher
branches. Frozen strict-child laws supply every recursive request charge.
CheckedInstructionCredit derives actual accepted child code and rejected
sentinel code at their exact checked body state. Original source profiles
bound the schedules even when returned constructor results grow.

InstructionStep proves that every actual yielded instruction consumes at least
one credit. Cold node publication retains its captured finish. Cold edge
publication retains the actual checked body effect and captured edge finish.
Warm returns retain the exact physical continuation. InstructionTrace bounds
every actual physical prefix by the original whole-request budget.

## Complete query producer

InitialInstructionBudget.complete constructs its own physical receipt from
the established original semantic domain, active-cache admission, and word
ranges. It bounds that same trace by nodeBudget. It derives exact execute at
nodeBudget plus one, current store and returned mass, and both constructor
identity supplies. Domain allocation is at most nodeBudget.

The initial endpoint derives word ranges from initial counters and finite
domain room. It takes closed original operands, Good, SemanticReady, and
Idle. Idle permits populated completed tables. It does not require empty
native or equality tables. No physical trace, future WordRanges, later entry
counter, instruction count, or desired result law is an input to this endpoint.
The actual receipt retains all native and equality-operation state.

The budget uses the least successful semantic requiredFuel. This is an
initial-source mathematical value. It is noncomputable in the current
declaration. The proof does not select it from the completed physical trace.
A computed syntax-only bound is a further theorem.

The bound counts yielded checked instructions. Observing the final pure done
requires one more execute unit. One Work or optionalBinder counts once.
Its internal constructor execution and solver work need separate measures.
Logical mass does not measure bytes or total memory capacity. The new
exported initial receipt gives physical and resource results. Existing
contextual language laws remain separate components to compose on the same
trace. This checkpoint does not claim complete serial public semantics.

## Remaining work

1. Bound semantic requiredFuel by computed initial syntax and finite source
   inventory measures. Retain reset, swap, Mu, references, unions, and checked
   edge children. Do not replace the full source family by ordinary trees.
2. Compose complete queries that consume their actual preceding results.
   Forecast later source profiles, semantic rank, word admission, and numeric
   resources from the original input and call count. Retain populated native,
   equality, and global caches. Compose current contextual laws and rebase
   certificates on the same actual trace.
3. Complete general Target and Force misses, mixed Edit, and ClassPass from
   initial resources. Produce active and stored outer-descent certificates.
   Cover arbitrary constrained Mu bodies. Keep the source gate that accepts
   closed no-Mu endpoints independently of their own guard.
4. Prove repeated reduction convergence and remaining recursive callers.
   One complete pass is not a fixed point.
5. Complete current typing/refinement adapters, drawn fields, symbolic
   measures, errors, validation order, and generator rank order. Complete
   solver, runtime, IO, randomness, concrete capacity, and user-code adapters.
6. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

Preserve all earlier proofs, counterexamples, repairs, and marked drafts.
Keep the optimized interned core and older constructor and equality work.
Do not repeat completed causal mass, initial width, native instruction credit,
source-rebase, origin, Merge, selected-Operand, mixed-editor cap, or serial
optional-binder proofs.

## Validation and Haskell handoff

The pinned Lean 4.34.1 Audit passes 2884 jobs and 64123 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All eight final strict
production logs are empty. Validation comprises 63 public checks and eleven
constructive integration proofs.
All 74 full signature and axiom pairs pass in twelve groups. Six component
manifests verify 166 entries. The next-target source survey adds 23 entries.
Aggregate validation checks seven manifests with 189 entries.
Complete imported signatures, constructive
integrations, raw attempts, component manifests, and hashes are in
restart-evidence/20261017-native-instruction-budget.

Preservation retains 12943 starting files, 2875 older non-Audit production
proofs, all 239 Haskell files, all 206 active-package files, stashes, and three
other worktrees. All 77 frozen manifests retain their 641 entries.

No Haskell source change or new defect occurs. Root FINDINGS keeps current
repair status first. Field-pool repair b9219b9e is merged in c0cc8a05. The
Chain example returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds
retains opaque-pool evaluation. Reuse unchanged strict Nix, 798 examples plus
golden, Fourmolu, and Cabal-gild evidence. Record each later Haskell repair
with its failure, reproducer, affected paths, commit, checks, and upstream
status for external work.
