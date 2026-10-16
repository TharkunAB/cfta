import MicroCFTA.SourceCurrentAllocatedPartialGraph
import MicroCFTA.SourceCurrentAllocatedPartialMemoSound

/-!
# Actual allocated descent before a current recursive child call

The child uses the literal indexed descent at the current operation cache.
Its native state and every caller table stay unchanged. Actual allocation
derives the child payload and its inherited satisfaction obligation.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialDescent
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialMemoSound (Sound NodeLaw)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable {width : Nat}

/-- An actual descent preserves every component except the returned equality operations. -/
theorem components (before : Caller width) (combined : EqValue) (index : Nat) :
    (descend before combined index).1 = (SourceEqualityConstraintMemoAllocation.descend combined index before.checked.operations).1 ∧
    (descend before combined index).2.checked.native = before.checked.native ∧
    (descend before combined index).2.checked.operations = (SourceEqualityConstraintMemoAllocation.descend combined index before.checked.operations).2 ∧
    (descend before combined index).2.merge = before.merge ∧
    (descend before combined index).2.fourth = before.fourth ∧
    (descend before combined index).2.nodeResults = before.nodeResults ∧
    (descend before combined index).2.edgeResults = before.edgeResults := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The indexed child receives a ready literal payload in the same current caller. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Caller width) (combined : EqValue) (index : Nat) : Prop where
  ready : Ready (descend before combined index).2.checked
  admitted : At formulas solver inventory (descend before combined index).2.checked
  sound : Sound formulas solver (descend before combined index).2
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical (descend before combined index).2.checked)
  inherited : SourceEqualityConstraintAllocation.Ready (descend before combined index).2.checked.operations.constraints
    (descend before combined index).1
  payload : (descend before combined index).1.payload = SourceEqualityDescend.descend combined.payload index
  extension : SourceRecursiveIntersectionKernel.Extension before.checked.native.machine
    (descend before combined index).2.checked.native.machine

/-- Initial current invariants derive every actual indexed allocation receipt. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Caller width) (combined : EqValue) (index : Nat)
    (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
    (sound : Sound formulas solver before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints combined) :
    Receipt formulas solver inventory before combined index := by
  obtain ⟨valid, childReady, payload, growth⟩ := SourceEqualityConstraintMemoAllocation.descend_correct combined index
    before.checked.operations ready.good.operations inherited
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked)
      (physical (descend before combined index).2.checked) :=
    ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready,
      ⟨ready.semantic, ready.costs, valid, ready.good.fields.grows growth⟩, growth⟩
  have nextReady := SourceCurrentConjunctionAllocatedClassEntry.operations_ready before.checked _ ready valid growth
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before.checked
    ⟨before.checked.native.machine.heap, (SourceEqualityConstraintMemoAllocation.descend combined index before.checked.operations).2⟩ effects
  exact ⟨nextReady, admitted.advance _ extension, sound.advance formulas solver _ before.fourth before.merge effects,
    effects, childReady, payload, extension⟩

/-- A satisfied combined parent supplies the literal allocated constraint of each existing child. -/
theorem parent_satisfied (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Caller width) (combined : EqValue) (index : Nat)
    (receipt : Receipt formulas solver inventory before combined index)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints combined)
    (symbol : Symbol) (terms : List (Term Symbol)) (term : Term Symbol)
    (found : terms[index]? = some term)
    (satisfied : SourceEqualityPrecheck.Sat (.node symbol terms) combined.payload) :
    SourceEqualityPrecheck.Sat term (descend before combined index).1.payload := by
  rw [receipt.payload]
  exact SourceEqualityDescend.descend_sound combined.payload inherited.2 symbol terms index term found satisfied

/-- An actual child induction result uses the source descent payload without a second allocation. -/
theorem node_law (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Caller width) (combined : EqValue) (index : Nat)
    (receipt : Receipt formulas solver inventory before combined index)
    (value result : Value Symbol Guard)
    (law : NodeLaw formulas solver ⟨(descend before combined index).1, value⟩ result) :
    ∀ ambient term,
      (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) ∧
      (SourceEqualityPrecheck.Sat term (SourceEqualityDescend.descend combined.payload index) →
        (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term)) := by
  intro ambient term
  simpa only [receipt.payload] using law ambient term

end MicroCFTA.SourceCurrentAllocatedPartialDescent
