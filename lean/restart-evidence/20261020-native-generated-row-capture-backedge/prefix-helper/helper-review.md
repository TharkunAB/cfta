# Auxiliary normalized-prefix experiments

This package retains eight bounded experiments. It adds no official declaration, constructed example, canonical build, or complete public printer group. No working native checkpoint is claimed.

The checked_cbv% term elaborator asks Lean.Meta.Tactic.Cbv.cbvEntry for a normalized expression and its equality proof. It stores both in a subtype. The small API test passes kernel checking. Two materialized natural-number checkpoints compose with congrArg and equality transitivity. The checked theorem has no axioms. Rewriting through a dependent subtype projection fails. Exact execute_add composition must instead use execute_add.trans and congrArg on resume, then trans with the next checkpoint property.

On the actual V2 source data, full Outcome normalization fails at both sixteen-step and one-step checkpoints with the retained maximum recursion depth of 300000. Source-heap opacity does not fix the one-step full-state reduction. These attempts remain rejected diagnostics.

The checked_whnf% alternative stores a weak-head expression and definitional equality. Its algebraic execute32 equality passes with the standard three axioms. It does not establish an actual materialized sixteen-step checkpoint. The separate yielded-constructor proof fails. Diagnostic head inspection shows execute.match_1 with step as its discriminant, then lift.match_1, native step.match_5 and a projected value. The recursive head-inspection helper also has a termination diagnostic. These observations do not identify a concrete blocked native execution and do not prove that the prefix advanced.

The fixture owner later found a smaller reduction repair. The installed symbolic ground evaluator recognizes overloaded arithmetic applications but did not reduce the fixture's direct Nat.add applications efficiently. Local reflexive arithmetic bridge equalities registered with cbv_eval reduce the actual locator to 60. That arithmetic experiment belongs to the fixture owner. This package contains no duplicate arithmetic run. The normalized-prefix approach was stopped at the parent's instruction.

The original proposal to reduce the checked width to 32 does not satisfy the same existing resource certificate, which requires width at least 382. It was not used in these checks. The actual V2 experiments retain width 1024.

All eight jobs use pinned Lean 4.34.1, all linters, a five-minute cap, effective 4 GiB memory.max and memory.high, zero swap, and fresh usage above the stop threshold. Exact sources, logs and receipts remain. There are six unsuccessful checks and two auxiliary successful checks. The small API success and the weak-head algebraic success are not counted as native fixture validation. No native_decide, trustCompiler or additional axiom was introduced by the successful checks. Failed proof drafts contain sorryAx recovery reports and are explicitly unselected.

The proof examples remain temporary evidence. The official generated-row capture producer and its frozen source package are unchanged. The actual used generated Mu and captured initial row fixture remains with its owner. The arithmetic repair must pass that full fixture before any fixture success is claimed.
