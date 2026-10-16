# Current conjunction scan completion review

Timestamp: 2026-10-16 07:01 CEST. Independent read-only review after the reported GREEN1186 build. No proof source edits or builds were run.

Reviewed frozen source:

- `SourceCurrentConjunctionClassScan.lean`, SHA256 `46edf035a9e6890053ccd6caee25052ca293e42277e10bbba75529f84fdd5cd1`.
- `SourceCurrentConjunctionClassScanCompletion.lean`, SHA256 `b5fe7c3c9cb143f63f4294c7696a18478846a35d12c5058eabf6d13e10d9f427`.
- The actual checked seeded completion, gate field completion, memo lift, finite input inventory models, and contextual cache definitions.

No material proof or interface defect was found.

## Public finite premise

`finite` has initial `Ready`, original forest `Values`, proper natural paths, fourth-memo `Correct`, and `Ranges`. `Ready` contains physical `Good`, semantic heap readiness, costs, scoped returned cells, and native idleness. No whole-original-forest closedness is required.

`Ranges` does not assert callback success. It demands bounds only under actual gate traces. A false primary trace requires a tail range plan at its actual returned state. A true primary and true secondary trace require the tail plan after both heap advances. A true primary and false secondary trace require `SeededRanges` at the actual advanced anchor. Only an actual completed false memo answer requires the subsequent tail range plan. There is no suffix condition for a true answer.

`SeededRanges` contains only actual reached native `WordRanges`. Projection and tail completion are antecedents that select the reached state; they are not existential completion premises. Actual gate completion, supported projection completion, strong checked native scope completion, and current conjunction memo completion produce these antecedents in the proof. The public endpoint therefore constructs the finite reached graph without a supplied completed native query, decision, scan, result law, or future readiness premise. Word-range discharge remains explicit.

## Whole-state and operation continuity

Gate steps retain the exact equality-operation state and native cells through `advanceHeap`. The seeded graph uses the current checked `NativeDemand` interpreter. Its first-seed rotation is literal `rest ++ [seed]`; each fold projects its head, completes its tail, and then issues the native request at that returned state. The native trace threads the whole checked state, including both memo tables, the domain cache, and the returned equality-operation cache.

On the false-secondary branch, `false_class_complete` starts before that secondary gate and returns `queryEffects` that includes both the secondary gate and the entire seeded query. Thus `firstEffects.trans queryEffects` includes every gate effect once; no anchor state or equality cache is lost. The proof uses those same effects to derive the returned query readiness and to grow fourth-memo correctness.

The current conjunction call receives `physical middle`, including the exact checked query's returned operation cache. Its physical return becomes `advancePhysical middle later`. The tail receives the actual `savedMemo`, not the initial memo. No operation tables, native cells, or domain cache are reset. Native tables can change during a checked query; only the gate and conjunction-only advances claim literal table retention.

## Fourth memo and early stop

The selected branch grows `Correct` across the primary heap effects and then invokes the tail. The skipped branch grows it across both gates before invoking the tail. The continued branch grows it across the combined secondary/query effects, verifies the actual current call, and invokes the tail with its returned memo and physical invariants. Its final `Extends` composes the actual call's retention with the tail's retention. The stopped branch returns the verified call's final correctness and retention directly. It has no tail scan or suffix range demand.

Original values remain available through actual `Keeps` effects in every branch. Selected paths preserve order and multiplicity as a sublist. An early rejected class is proved to be an original reached class. This membership statement is not a semantic refutation theorem.

## Source and claim scope

Current `Equality/Operations.hs:207-226` partitions ordered original classes using the primary mode, tests refused classes using the secondary mode, and calls `provablyEmpty` only when the secondary check is false. `intersectList` uses the first operand as seed and right-folds the rest. The new graph follows these branch conditions and stops before the suffix on a true answer. The ordinary physical entry must still supply the source's ordered normalized class list and the concrete `unconstrained` and `reachesConstrainedMu` functions.

The source partition and projected list are lazy. The graph records a chosen completed resident schedule. It does not prove GHC forcing or allocation order, pending publication, runtime global memo transfer, concurrency, or concrete container equivalence. The three global gate memo receipts remain separate. Outer precheck, selected class edits, and full constrained caller termination are not conclusions of this finite scan theorem.

`Correct` and `AnswerSound` describe the actual generated query. They do not establish that a true answer refutes the original equality class. The source headers correctly retain that semantic query bridge as an open obligation.

## Exact next semantic obligation

The smallest useful public language target is a checked-seeded counterpart of the old `SourceCurrentSecondaryRefusedClassQuery.class_witness`:

Given the actual false secondary trace, initial legitimate semantic cache invariant, proper supported paths, and the actual new `SourceCurrentAllocatedSeededQuery.Seeded` trace, an accepted original forest and a satisfied nontrivial original class must yield a common subtree accepted by the actual returned query. It can also retain the existing strict subtree-height bound. Full query-language equivalence is stronger than the original-class refutation needs. This one inclusion, followed by the current memo's true-answer exclusion, suffices to refute the original class and then a stopped scan.

The projection part already has anchored accepted-subtree inclusion. The missing part is independent intersection completeness for each actual checked native fold request, including generated tail operands and warm hits. Scope and physical validity do not establish that language fact.

`InputInventoryModels.finiteInput` ranges over inputs reachable from listed closed original operands in one fixed source heap. A newly allocated projection or intersection result can have a fresh identity that is absent from that source's physical view. `ContextCache.NodeLaw` and `EdgeLaw` are conditional on `NodeInputs` and `EdgeInputs`, which include model validity. A cached law for an earlier narrower model can therefore be vacuous on a request newly admitted by a larger model. `advance_contextual` retains the same fixed model and cells; it does not enlarge the model or prove new input membership.

A precise supporting transport target must derive admission of actual new request operands in a finite current model and transport old returned-cell laws into that model. It needs language and derivation-rank agreement on the old covered input domain, including names used by old request pair contexts. It must also rule out treating a previously out-of-domain cached request as newly justified merely by enlarging `valid`. One suitable route maintains coverage of every relevant cached request by its old model, then proves conservative model extension and view readback stability through actual heap growth. Another route stores model-parametric contextual certificates when the actual cells finish. Either route must derive the cache transfer from reached provenance, not require future `Contextual`, final `NodeLaw`, or whole-query success as a public hypothesis.

After that admission/transport lemma, actual fold induction can thread the derived semantic cache invariant, prove common-term retention at every returned native request, and reuse the existing class witness argument. Unrelated original siblings can remain open throughout.
