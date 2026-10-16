# Frontend proof coverage after ccebf0f7

The incoming source preserves the interned core and Sized byte for byte.
The current checked native/class/caller proofs remain attached to that core.
The whole-library target includes these frontend changes, but existing
component proofs do not automatically cover them.

* SourceTypingRules/SourceTypingRulesLanguage and SourceTypingFinite model
  fixed Int remaining and root env=[]. They remain a current empty-input
  Nesting slice. Root input environments need an additive row/closure transfer.
  Binders needs Maybe remaining, actual bounded-env closure/visited-map proof,
  cyclic term semantics, size-indexed completeness, and ambiguity treatment.
  A decreasing Nesting rank must not be reused to claim Binders completion.
* SourceTypingFieldValidation covers resolved field shape logic. Derivation
  from actual HasFTA metadata, dynamic variable callbacks, errors, codec,
  fromRows/SCC, and complete generator/rank behavior remain separate adapters.
  SourceTypingRelevantHelperOrder still concerns the unchanged relevant-type
  metadata order. It is not a proof of the new binder/rule language.
* SourceCurriedDefaulting has the OLD three-branch narrowHeads and old
  Defaulting map API. Exact local filtering can be transferred only on the
  no-?any slice. The new SourceCurrentCurriedDefaulting adapter now proves
  current four-branch filtering and that historical agreement. It does not
  prove domainNodes, domainDepth, kind roles, path-variable correlations,
  GHC instances, or total synthesis completeness.
* SourceProgramRunAccounting remains a typed-run/proposal accounting
  component. It does not identify a marker run with a concrete domain type.
  SourceGhcFitNormalForms and SourceGhcFitRanking cover separate filter/rank
  algorithms, not the new default-on type-domain construction or contextual
  equivalence of Haskell programs.
* SourceCurrentMeasureEvaluation/Folding and SourceDeriveNodeViewNames
  continue to cover their unchanged local evaluator/folding/name phase.
  deriveLTAOn* requires a NEW acyclic state-row induction relating actual
  constructorGenerator, atomic decode/toLiteral agreement, annotation
  formulas, contracts, generated refinement constraints, codec, and ranks.
  The source rejects cycles and constraints rather than solving them.

Useful next frontend theorem order:

1. Current marker filter and exact no-?any agreement (completed bounded module).
2. Typed root-input row semantics and actual close-map coverage.
3. Finite closure for Binders on actual finite rule/callback data, followed by
   size-indexed language/rank linkage with an explicit unambiguity condition.
4. deriveLTAOn acyclic per-state language as input-automaton language filtered
   by the invariant, with actual atom decoding and constructor code domain.
5. Conservative GHC instance-context domain approximation and bounded
   domainNodes unrolling, followed by run-marker/proposal/checker wiring.

No existing proof source is renamed or overwritten. Historical interfaces
must stay labeled by their actual restricted source domain.
