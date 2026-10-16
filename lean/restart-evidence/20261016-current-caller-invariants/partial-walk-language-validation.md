# Actual allocated child-walk semantic induction steps

Validated on 2026-10-16. The new source module is SourceCurrentAllocatedPartialWalkLanguage.lean. It is an additive component proof.

DescendedSat fixes the original combined payload and source index. Each term at offset k must satisfy the literal SourceEqualityDescend.descend combined.payload (index+k). The head and tail rules preserve that offset convention. of_parent derives all offsets from actual parent satisfaction and the physical payload WellFormed law.

WalkLaw and ChildrenLaw are indexed by the actual current Walk and Children graphs. Each law supplies unconditional All2 narrowing. Walk preservation requires DescendedSat. Children preservation requires satisfaction of the original combined parent payload. Both laws use the same independent PCS meaning, arbitrary ambient environment, exact result order, and exact input order. They allow open inputs.

walk_cons consumes the smaller actual head NodeCall law, actual next-offset tail WalkLaw, and the equation for the literal allocated descended head payload. walk_cons_receipt derives that equation from the existing physical PartialDescent.Receipt. children_live uses the pure source descend_sound theorem to discharge all child satisfaction obligations. children_contradiction has no child call or result law premise and follows the literal source erasure branch.

These are explicit induction combinators. This module does not prove the whole recursive caller correct or terminating. It does not supply a future NodeLaw callback, future physical readiness, memo Sound, finite range plan, or runtime adapter. Those obligations stay separate. No older source, Haskell source, Audit, docs, or Git metadata was edited.

Focused canonical build-2 exits 0 with 1397 jobs. Its only warning is the existing unused inputs variable in InternedFreshOrdinaryClosedCompletion. Build-1 also succeeded but recorded new helper lint warnings; the final source removes them. Direct-1 records initial elaboration errors. Direct-2 succeeds, and the final canonical build and final public/kernel probes validate the frozen source.

Public probes: 12 axiom reports and 19 full signatures (12 theorem endpoints plus the satisfaction/law definitions and four law projections). Four integration kernels each have an axiom report and full signature: two actual calls at an arbitrary offset; a live two-child parent that derives child satisfaction from the parent; contradiction with no recursive calls; and a real physical descent receipt composed with one actual child call. All 16 reports and 23 checks pass with exit 0. Final logs contain no errors, warnings, or sorryAx. The only axioms are propext, Classical.choice, and Quot.sound; some endpoints are axiom-free.
