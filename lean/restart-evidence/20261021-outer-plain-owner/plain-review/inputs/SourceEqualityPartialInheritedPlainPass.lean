import MicroCFTA.SourceEqualityPartialPlainSource

/-!
# Actual empty-own equality passes with arbitrary inherited payloads

The source precheck selects unchanged, contradiction, or an empty class
list. The live empty list retains selection, required paths, the fold,
and final empty propagation. No native intersection request is reached.
-/
namespace MicroCFTA.SourceEqualityPartialInheritedPlainPass
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained

/-- Empty own payloads select only the three concrete non-narrowing source branches. -/
theorem precheck_cases (inherited : SourceEqualityPrecheck.Constraint) :
    SourceEqualityPrecheck.precheck (some []) inherited = .ok .unchanged ∨
      SourceEqualityPrecheck.precheck (some []) inherited = .ok .emptyChildren ∨
      SourceEqualityPrecheck.precheck (some []) inherited = .ok (.classes []) := by
  by_cases first : (SourceEqualityPrecheck.isEmpty (some []) && SourceEqualityPrecheck.isEmpty inherited) = true
  · exact Or.inl (by simp only [SourceEqualityPrecheck.precheck, first] <;> rfl)
  · by_cases second : SourceEqualityPrecheck.rejects (SourceEqualityPrecheck.combine (some []) inherited) = true
    · exact Or.inr (Or.inl (by simp only [SourceEqualityPrecheck.precheck, first, second] <;> rfl))
    · exact Or.inr (Or.inr (by simp only [SourceEqualityPrecheck.precheck, first, second] <;> rfl))

/-- Final source propagation keeps the original forest or erases every slot. -/
theorem propagate_shape (values : List (Value Symbol Guard)) :
    EqualityLeafProjectionRuntimeEmpty.propagate values = values ∨
      EqualityLeafProjectionRuntimeEmpty.propagate values = EqualityLeafProjectionRuntimeEmpty.erase values := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual empty selected list still executes its literal required-path and final propagation stages. -/
theorem empty_stages (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :
    SourceEqualitySelectedClassFold.Execution source top conjoin SourceMemoGate.plain top [] values before
      [] before.machine.heap values before.machine.heap (EqualityLeafProjectionRuntimeEmpty.propagate values) before := by
  refine ⟨⟨.nil, 0, 0, ?_⟩, .done .nil⟩
  simpa [SourceEqualitySelectedRequired.paths, InternedSourceClassSelection.selected, EqualityNormalize.canonicalClass] using
    SourceEqualityRequiredExecution.requireAll_identity 0 0 values before.machine.heap

/-- Every inherited payload has a finite actual empty-own pass with unchanged constructor heap and bounded structural output. -/
theorem complete (inherited : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) :
    ∃ results, SourceEqualityOnePassGraph.Execution source top conjoin SourceMemoGate.plain top (some []) inherited values before (.ok results) before ∧
      (results = values ∨ results = EqualityLeafProjectionRuntimeEmpty.erase values) := by
  rcases precheck_cases inherited with unchanged | contradiction | live
  · exact ⟨values, .unchanged unchanged, Or.inl rfl⟩
  · exact ⟨_, .emptyChildren contradiction, Or.inr rfl⟩
  · exact ⟨_, .live live (empty_stages values before), propagate_shape values⟩

end MicroCFTA.SourceEqualityPartialInheritedPlainPass
