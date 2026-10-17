# Independent joint source execution review

Reviewed on 2026-10-17 at 04:55 CEST. No material defect was found. This review changes no production file.

The final reviewed source is `SourceCurrentConstrainedCapKernelJointCalls.lean` (155 lines, SHA-256 `f51256dfea5b968b709bd61bda943584591cc24190808659c4086e6c1a9fbd1f`) and `SourceCurrentConstrainedCapKernelJointExecution.lean` (133 lines, SHA-256 `bad45c7705ca6282fa5becb5255b300828641d166ce2d711f2b35b4c52b9fe47`). The earlier Calls hash `a0a42e84` is a historical input. Its direct-3 source and warning log remain in the owner's evidence. The final source removes the unused global instance and retains the explicit instance needed by `mu_joint`.

## Proof and premises

`KernelJoint.Context` (lines 27–37) contains current kernel validity, semantic and causal guard heaps, and growth and issued-key history from one fixed source. `Checked` (lines 40–42) asserts laws at successful returns of the actual bounded execution. It does not assert that a return exists. `Calls` is a local induction interface. `execute_joint` (Execution lines 120–131) discharges that interface by induction on source fuel. Its public premises are source Facts and closure of the chosen annotation under the empty guard and conjunction. The expanded Calls contract also requires the actual initial Context and domain representation, original binding witnesses, source-original available and covered operands, and input caps. No future result, completed recursive body, or range oracle is a premise of `execute_joint`.

`onNode_joint` (Execution lines 26–117) follows the literal decision. Empty, self, repeated, reset and swap cases use their actual branch facts. Reset obtains closed operands before changing to the empty domain. Repeated uses the actual selected numeric pair and original binding witnesses to establish its source weight. Union and ordinary cases use the actual ordered row helpers. Unsupported branches fail.

`mu_joint` (Calls lines 37–123) records the actual entered key and retains the original source operands and bindings. It applies the smaller actual call to the literal bodies. Body rank equality (lines 71–76) transfers the classifier. It is not an execution termination argument: Mu recursion can keep the same positive rank. The source-fuel induction supplies the smaller call.

The zero-rank case (Calls lines 102–114) reuses the same actual smaller-body return at cap depth zero. This derives annotation of that returned value before the hereditary optional-binder theorem is applied. It does not assume that value is annotated. The positive case (lines 115–116) uses the actual returned cap, classifier, derived probe freshness and causal GuardHeap. NativeBinderReturn selects the actual final constructor winner. No desired cap law for a warm winner is inserted as a premise here.

`reference_joint` (Calls lines 126–153) reads the exact original Mu binding under the current source history. That binding is hereditary and has rank zero. The actual found value supplies source availability, coverage and original syntax to the smaller call. Missing names fail. The proof does not infer probe freshness from interned-only Covered: actual output Scope provides that stronger fact in the Mu case.

## Imported validation

The final imported public source prints axioms and fully explicit signatures for all five public declarations across Calls and Execution: `body_rank`, `mu_joint`, `reference_joint`, `onNode_joint`, and `execute_joint`. The final public log has no diagnostics. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms.

The independent `productive_mixed_query` kernel constructs the closed source pair `mu x.(const | step x)` and a false-guard `step(const)` through actual buildMany. It derives physical Facts, semantic and causal guard heaps, and both input caps from the source producers. It computes the actual fuel-16 intersection and obtains the constrained second operand as the result. Applying `execute_joint` to that actual return derives Cap 1, the source-weight classifier, empty pair Scope, final GuardHeap, SemanticHeap and source growth at the same returned machine. The kernel takes no supplied execution, output law, headroom or WordRanges premise. It exercises productive recursion with a nonhereditary ordinary operand.

The final kernel rerun uses the final Calls import. Public log `joint-execution-independent-public-1.log` and kernel log `joint-execution-independent-kernels-3.log` are clean. Kernel attempt 1 is retained; its failure was only dependent elimination before unfolding evaluateMany. Attempts 2 and 3 pass. The final whole Audit log reports 2816 jobs and 62897 dependency checks. Its only warning is the historical `InternedFreshOrdinaryClosedCompletion` unused variable warning.

## Scope

This is an actual source-kernel result-law producer for every recursion bound. It does not itself prove general bounded execution succeeds. Independent cold completion can provide existence; the current NativeJointClosed cold endpoint still states its WordRanges premise. The fixture proves existence only for its literal source pair. Pair rank is not claimed as a general native termination measure. The current checked native bridge and its exact generic-kernel Meaning remain distinct from a whole-library Haskell correspondence or general constrained selected-path termination. No new host-language defect is claimed.
