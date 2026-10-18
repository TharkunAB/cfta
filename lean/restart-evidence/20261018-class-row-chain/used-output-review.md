# Actual used-binder output tags and strict body induction step

The production module is `SourceCurrentUsedBinderOutputTags`.
It proves bare-reference and empty reflection for two actual source builds.
The source syntax can contain arbitrary nested smart and raw binders.
The captures can contain arbitrary available Mu values.
The alias tests use the live source support and an explicit Depth anchor.
They do not require injective varying labels or exclude captured Depth aliases.

`bare` reflects actual returned Values through actual build profiles.
`scoped_bare` and `depth_bare` derive its alias tests from the source input relation.
`empty` needs the same symbolic input list but no alias premise.
These theorems do not infer literal equality of the two returned records.

`callback_induction_step` constructs both raw source calls and both self filters.
It retains their exact sequential heaps, physical growth, issued identities,
Ready states, result availability, and actual publication histories.
It derives the bare-self parity required by the checked root-filter theorem.
It uses `StrictBodyIH` only at the actual strictly smaller source body.
The hypothesis quantifies over smaller source syntax and actual executions.
It is an explicit induction premise, not a theorem that closes the induction.

`publication_induction_step` uses the actual historical publication callbacks.
It derives the local input aliases and returned bare-self parity internally.
It then derives RootMatch for the actual filtered ordinary and body values.
It neither replaces the selected older winner with the current candidate nor
asserts a recursive relation for that older winner's body.

The first constructed case starts from a closed nested USED source build.
It recovers an actual retained writer and checks an ignored warm callback.
The second case checks nested smart cleanup with a captured Depth alias.
Its dead rows execute nested binders, and its same-heap replay is literal.
Both cases check actual returned output tags rather than assumed output laws.

The remaining general obligation is to discharge the uniform strict body
induction at the nested used-Mu case and retain it for actual earlier winners.
No general source congruence, outer termination, or Haskell defect is claimed.
All failed numbered attempts remain in this component.

Selected checks: production direct-7 has an empty log.
Canonical-1 completed 580 jobs. Public-1 checks all seven public heads.
Kernels-4 has an empty log. Kernels-public-1 prints both constructed proofs.
Both public groups use all eight explicit flags and only the standard three axioms.
Every selected run has effective memory.max/high 4294967296 and swap.max 0.
The earlier failed membership/context fixture attempts remain unselected.
