import MicroCFTA.SourceCurrentOuterExecutionAncestry
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Literal equality-operation growth without result invariants

Every operation retains existing cache entries, including on malformed
inputs and stopped outcomes. These proofs establish growth only. They do
not establish result correctness or completed-table validity.
-/
namespace MicroCFTA.SourceCurrentOperationGrowth
open Cache SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Grows)

private theorem trans {before middle after : State} (first : Grows before middle)
    (last : Grows middle after) : Grows before after :=
  SourceCurrentConjunctionEquality.grows_trans first last

private theorem cached_combine (first second : Value) (before : State) :
    Grows before (SourceEqualityConstraintMemoAllocation.combineCached first second before).2 := by
  unfold SourceEqualityConstraintMemoAllocation.combineCached
  try dsimp only
  split <;> try dsimp only
  · exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · split <;> try dsimp only
    · exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · exact ⟨intern_steps _ _,keepFirst_extends _ _ _,extends_refl _⟩

/-- Actual combination retains the interner and both completed tables on every outcome. -/
theorem combine (first second : Value) (before : State) :
    Grows before (SourceEqualityConstraintMemoAllocation.combine first second before).2 := by
  cases first with
  | contradiction => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | live identity records =>
    cases second with
    | contradiction => exact SourceEqualityConstraintMemoAllocation.grows_refl _
    | live other remaining =>
      cases records <;> cases remaining
      all_goals first | exact SourceEqualityConstraintMemoAllocation.grows_refl _ | exact cached_combine _ _ _

/-- Actual indexed descent retains all old operation entries, independently of input readiness. -/
theorem descend (input : Value) (index : Nat) (before : State) :
    Grows before (SourceEqualityConstraintMemoAllocation.descend input index before).2 := by
  cases input with
  | contradiction => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | live identity records =>
    cases records with
    | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
    | cons head tail =>
      unfold SourceEqualityConstraintMemoAllocation.descend SourceEqualityConstraintMemoAllocation.descendCached
      try dsimp only
      split <;> try dsimp only
      · exact SourceEqualityConstraintMemoAllocation.grows_refl _
      · exact ⟨intern_steps _ _,extends_refl _,keepFirst_extends _ _ _⟩

private theorem construct (classes : Option EqualityNormalize.Constraints)
    (before : Cache.State SourceEqualityPartialConstraintKey.Key) :
    Cache.Steps before (SourceEqualityConstraintAllocation.construct classes before).2 := by
  unfold SourceEqualityConstraintAllocation.construct
  try dsimp only
  split <;> try dsimp only
  · exact .refl _
  · exact intern_steps _ _

private theorem demand (plan : SourceEqualityGuardAllocationPlan.Plan) (before : State) :
    Grows before (SourceEqualityGuardAllocation.demand plan before).2 := by
  induction plan generalizing before with
  | empty => exact ⟨intern_steps _ _,extends_refl _,extends_refl _⟩
  | pair first second => exact ⟨construct _ _,extends_refl _,extends_refl _⟩
  | combine first second ihFirst ihSecond =>
    unfold SourceEqualityGuardAllocation.demand
    try dsimp only
    split <;> try dsimp only
    · exact ihFirst _
    · exact ihFirst _
    · split <;> try dsimp only
      · exact trans (ihFirst _) (ihSecond _)
      · exact trans (ihFirst _) (trans (ihSecond _) (combine _ _ _))

private theorem positive (guard : SourceGuards.Guard Formula) (before : State) :
    Grows before (SourceEqualityGuardAllocation.demandPositive guard before).2 := by
  unfold SourceEqualityGuardAllocation.demandPositive
  try dsimp only
  split <;> try dsimp only
  · exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · exact demand _ _

private theorem accessor_value (stored : Value) (guard : SourceGuards.Guard Formula) (before : State) :
    Grows before (SourceEqualityAccessorAllocation.equalities stored guard before).2 := by
  unfold SourceEqualityAccessorAllocation.equalities
  try dsimp only
  split <;> try dsimp only
  · exact positive _ _
  · exact positive _ _
  · exact positive _ _
  · exact trans (positive _ _) (combine _ _ _)

/-- The source accessor retains all operation entries on successful and stopped loads. -/
theorem accessor (guard : SourceSymbolicIndex.Constraint Formula) (before : State) :
    Grows before (SourceCurrentConjunctionEquality.accessor guard before).2 := by
  unfold SourceCurrentConjunctionEquality.accessor
  try dsimp only
  split <;> try dsimp only
  · exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · exact accessor_value _ _ _

private theorem check (stored : Value) (guard : SourceGuards.Guard Formula) (arity : Nat) (before : State) :
    Grows before (SourceEqualityMkEdgeAllocation.check stored guard arity before).2 := by
  unfold SourceEqualityMkEdgeAllocation.check
  try dsimp only
  split <;> try dsimp only
  · exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · exact accessor_value _ _ _

/-- Sentinel construction retains actual allocation receipts and both completed memo tables. -/
theorem emptyField (before : State) : Grows before (SourceEqualityMkEdgeAllocation.emptyField before) :=
  ⟨intern_steps _ _,extends_refl _,extends_refl _⟩

private theorem edge_prefix [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : SourceEqualityConjoinAllocation.Constraint Formula) (left right : Nat) (before : State) :
    Grows before (SourceEqualityIntersectionEdgeAllocation.run le first second left right before).2 := by
  unfold SourceEqualityIntersectionEdgeAllocation.run
  try dsimp only
  split <;> try dsimp only
  · exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · split <;> try dsimp only
    · exact combine _ _ _
    · split <;> exact trans (combine _ _ _) (check _ _ _ _)

private theorem native_body (request : SourceRecursiveIntersectionThunks.EdgeRequest
      (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (next : InternedConstructorTemplates.EdgeValue (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula) → SourceRecursiveIntersectionCode.Code _ _ Output)
    (before : SourceEqualityNativeDemand.State width) :
    Grows before.operations (SourceEqualityNativeDemand.body request next before).state.operations := by
  unfold SourceEqualityNativeDemand.body
  try dsimp only
  split <;> try dsimp only
  · exact emptyField _
  · split <;> try dsimp only
    · exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · split <;> try dsimp only
      · exact SourceEqualityConstraintMemoAllocation.grows_refl _
      · exact SourceEqualityConstraintMemoAllocation.grows_refl _
      · split <;> try dsimp only
        · exact edge_prefix _ _ _ _ _ _
        · exact trans (edge_prefix _ _ _ _ _ _) (emptyField _)
        · exact trans (edge_prefix _ _ _ _ _ _) (emptyField _)
        · exact edge_prefix _ _ _ _ _ _

variable [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
  [DecidableEq (InternedConstructorTemplates.EdgeKey (SourceObservations.Label FullSyntax.Formula)
    (SourceSymbolicIndex.Constraint FullSyntax.Formula))]

/-- Every literal checked native instruction retains all equality operation entries. -/
theorem native_step (control : SourceEqualityNativeDemand.Control Output)
    (before : SourceEqualityNativeDemand.State width) :
    Grows before.operations (SourceEqualityNativeDemand.step control before).state.operations := by
  cases control with
  | edgeBody request next => exact native_body request next before
  | code code =>
    rw [SourceEqualityNativeDemandOperations.step_code_operations]
    exact SourceEqualityConstraintMemoAllocation.grows_refl _

/-- Every bounded native outcome derives operation growth without a reached-field certificate. -/
theorem native (fuel : Nat) (control : SourceEqualityNativeDemand.Control Output)
    (before : SourceEqualityNativeDemand.State width) :
    Grows before.operations (SourceEqualityNativeDemand.execute fuel control before).state.operations := by
  induction fuel generalizing control before with
  | zero => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | succ fuel ih =>
    have first := native_step control before
    cases actual : SourceEqualityNativeDemand.step control before with
    | yielded next after =>
      have first : Grows before.operations after.operations := by simpa only [actual,SourceEqualityNativeDemand.Outcome.state] using first
      simpa only [SourceEqualityNativeDemand.execute,actual] using trans first (ih next after)
    | done | failed | constraintError | blocked =>
      simpa only [SourceEqualityNativeDemand.execute,actual,SourceEqualityNativeDemand.Outcome.state] using first

end MicroCFTA.SourceCurrentOperationGrowth
