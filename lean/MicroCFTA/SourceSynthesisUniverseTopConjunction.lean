import MicroCFTA.SourceSynthesisGeneralizeSyntax
import MicroCFTA.SourceEqualityPartialConjoinAllocation

/-!
# Physical top conjunction for the synthesis universe

Actual source conjunction retains both fields of the top constraint.
Two allocated live empty equality payloads take the explicit source shortcut.
That shortcut preserves the equality operation state. Positive Top demand
instead calls the empty-payload interner. These laws do not describe runtime
temporary allocations or establish GHC evaluation correspondence.
-/
namespace MicroCFTA.SourceSynthesisUniverseTopConjunction

variable {Formula : Type}

/-- Canonical guard conjunction removes both top operands before sorting. -/
theorem merge_top [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool) :
    GuardConjunction.merge le .top .top = .top := by
  simp [GuardConjunction.merge, GuardConjunction.normalize, GuardConjunction.atoms,
    GuardConjunction.canonical, GuardConjunction.conjoin]

/-- Both physical constraint fields remain exactly the actual source top fields. -/
theorem conjoin_top [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool) :
    SourceEqualityConstraintConstructors.conjoin le
      SourceEqualityConstraintConstructors.top SourceEqualityConstraintConstructors.top =
      SourceEqualityConstraintConstructors.top := by
  change (⟨some [], GuardConjunction.merge le .top .top⟩ : SourceSymbolicIndex.Constraint Formula) =
    ⟨some [], .top⟩
  rw [merge_top]

/-- Retain an actual live empty equality identity and the literal top guard. -/
def allocatedTop (identity : Nat) : SourceEqualityConjoinAllocation.Constraint Formula :=
  ⟨.live identity [], .top⟩

/-- The complete allocated readback has the original source top fields. -/
theorem allocatedTop_readback (identity : Nat) :
    SourceEqualityConjoinAllocation.readback (allocatedTop (Formula := Formula) identity) =
      SourceEqualityConstraintConstructors.top := rfl

/-- Literal top readback derives an empty stored record list and its actual identity. -/
theorem readback_top_iff (constraint : SourceEqualityConjoinAllocation.Constraint Formula) :
    SourceEqualityConjoinAllocation.readback constraint = SourceEqualityConstraintConstructors.top ↔
      ∃ identity, constraint = allocatedTop identity := by
  constructor
  · intro same
    cases constraint with
    | mk stored guard =>
        have guardTop := congrArg SourceSymbolicIndex.Constraint.guard same
        change guard = .top at guardTop
        subst guard
        have equalities := congrArg SourceSymbolicIndex.Constraint.equalities same
        cases stored with
        | contradiction =>
            simp [SourceEqualityConjoinAllocation.readback, SourceEqualityAccessorAllocation.constraint,
              SourceEqualityConstraintAllocation.Value.payload, SourceEqualityInheritedPayload.classes,
              SourceEqualityConstraintConstructors.top] at equalities
        | live identity records =>
            have empty : records = [] := by
              simpa [SourceEqualityConjoinAllocation.readback, SourceEqualityAccessorAllocation.constraint,
                SourceEqualityConstraintAllocation.Value.payload, SourceEqualityInheritedPayload.classes,
                SourceEqualityConstraintConstructors.top] using equalities
            subst records
            exact ⟨identity, rfl⟩
  · rintro ⟨identity, rfl⟩
    exact allocatedTop_readback identity

/-- Two live empty payloads bypass the operation memo and the equality interner. -/
theorem allocatedTop_conjoin [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Nat) (before : SourceEqualityConstraintMemoAllocation.State) :
    SourceEqualityConjoinAllocation.conjoin le (allocatedTop first) (allocatedTop second) before =
      (.ok (allocatedTop first), before) := by
  simp only [SourceEqualityConjoinAllocation.conjoin, allocatedTop,
    SourceEqualityConstraintMemoAllocation.combine, Except.map, merge_top]

/-- Literal source top fields derive the explicit unchanged-state conjunction branch. -/
theorem allocated_conjoin_top [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : SourceEqualityConjoinAllocation.Constraint Formula)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (firstTop : SourceEqualityConjoinAllocation.readback first = SourceEqualityConstraintConstructors.top)
    (secondTop : SourceEqualityConjoinAllocation.readback second = SourceEqualityConstraintConstructors.top) :
    SourceEqualityConjoinAllocation.conjoin le first second before = (.ok first, before) := by
  obtain ⟨firstIdentity, rfl⟩ := (readback_top_iff first).mp firstTop
  obtain ⟨secondIdentity, rfl⟩ := (readback_top_iff second).mp secondTop
  exact allocatedTop_conjoin le firstIdentity secondIdentity before

/-- Positive Top syntax retains its delayed empty equality constructor. -/
theorem positive_top_plan :
    SourceEqualityGuardAllocationPlan.make (SourceGuards.Guard.top (Formula := Formula)) =
      some .empty := rfl

/-- Demanding the Top plan retains the actual empty-payload interner call and its effects. -/
theorem positive_top_demand (before : SourceEqualityConstraintMemoAllocation.State) :
    SourceEqualityGuardAllocation.demandPositive (SourceGuards.Guard.top (Formula := Formula)) before =
      (.ok (some (SourceEqualityConstraintAllocation.intern (some []) before.constraints).1),
        {before with constraints := (SourceEqualityConstraintAllocation.intern (some []) before.constraints).2}) := rfl

section Concrete
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

/-- The actual native-edge conjunction discharges the universe body's physical top premise. -/
theorem native_conjoin_top :
    SourceEqualityPCSNativeEdge.conjoin SourceSynthesisGeneralizeSyntax.top SourceSynthesisGeneralizeSyntax.top =
      SourceSynthesisGeneralizeSyntax.top :=
  conjoin_top GuardStructuralOrder.le

/-- The recursive result allocation adapter preserves its entire state on actual top operands. -/
theorem partial_run_top
    (first second : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (firstTop : SourceEqualityConjoinAllocation.readback first = SourceSynthesisGeneralizeSyntax.top)
    (secondTop : SourceEqualityConjoinAllocation.readback second = SourceSynthesisGeneralizeSyntax.top) :
    SourceEqualityPartialConjoinAllocation.run first second before = (.ok first, before) :=
  allocated_conjoin_top GuardStructuralOrder.le first second before firstTop secondTop

end Concrete
end MicroCFTA.SourceSynthesisUniverseTopConjunction
