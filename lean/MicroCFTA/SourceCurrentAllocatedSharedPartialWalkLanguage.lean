import MicroCFTA.SourceCurrentAllocatedPartialWalkLanguage
import MicroCFTA.SourceCurrentAllocatedSharedPartialGraph

/-!
# Language composition for actual indexed child requests

These lemmas are induction steps for the current recursive graph. Each
head law refers to its literal allocated descent request. The tail law
starts at the next source index. No whole-caller completion or cache law
is supplied by this module.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedPartialWalkLanguage
open Cache Language InternedConstructorTemplates InternedGuardedLanguage
open SourceCurrentAllocatedSharedPartialGraph (NodeCall Walk Children descend)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "holds" => SourceEqualityPCSGuard.holds
variable {width : Nat}

export SourceCurrentAllocatedPartialWalkLanguage (DescendedSat)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- An actual walk narrows each slot and preserves its descended-satisfying input terms. -/
structure WalkLaw {budget : Nat} {combined : EqValue} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    (_actual : Walk budget combined index values before results after) : Prop where
  narrows : ∀ ambient terms, All₂ (meaning (holds formulas solver) ambient) results terms →
    All₂ (meaning (holds formulas solver) ambient) values terms
  preserves : ∀ ambient terms, DescendedSat combined index terms →
    All₂ (meaning (holds formulas solver) ambient) values terms →
    All₂ (meaning (holds formulas solver) ambient) results terms

/-- An actual child branch narrows slots and preserves each inherited-satisfying parent. -/
structure ChildrenLaw {budget : Nat} {combined : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    (_actual : Children budget combined values before results after) : Prop where
  narrows : ∀ ambient terms, All₂ (meaning (holds formulas solver) ambient) results terms →
    All₂ (meaning (holds formulas solver) ambient) values terms
  preserves : ∀ ambient symbol terms, SourceEqualityPrecheck.Sat (.node symbol terms) combined.payload →
    All₂ (meaning (holds formulas solver) ambient) values terms →
    All₂ (meaning (holds formulas solver) ambient) results terms

/-- An empty actual walk preserves its only accepted forest. -/
theorem walk_nil (budget : Nat) (combined : EqValue) (index : Nat) (before : Caller width) :
    WalkLaw formulas solver (Walk.nil (budget := budget) (combined := combined) (index := index) (before := before)) :=
  ⟨fun _ _ accepted => accepted, fun _ _ _ accepted => accepted⟩

/-- The exact allocated head law and next-offset tail law compose in source order. -/
theorem walk_cons {budget : Nat} {combined : EqValue} {index : Nat}
    {value result : Value Symbol Guard} {values results : List (Value Symbol Guard)}
    {before middle after : Caller width}
    (head : NodeCall budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result middle)
    (tail : Walk budget combined (index + 1) values middle results after)
    (payload : (descend before combined index).1.payload = SourceEqualityDescend.descend combined.payload index)
    (headLaw : NodeLaw formulas solver ⟨(descend before combined index).1, value⟩ result)
    (tailLaw : WalkLaw formulas solver tail) : WalkLaw formulas solver (.cons head tail) := by
  refine ⟨?_, ?_⟩
  · intro ambient terms accepted
    cases accepted with
    | cons acceptedHead acceptedTail =>
        exact .cons ((headLaw ambient _).1 acceptedHead) (tailLaw.narrows ambient _ acceptedTail)
  · intro ambient terms satisfied accepted
    cases accepted with
    | cons acceptedHead acceptedTail =>
        have headSat := satisfied.head
        rw [← payload] at headSat
        exact .cons (((headLaw ambient _).2 headSat).mpr acceptedHead)
          (tailLaw.preserves ambient _ satisfied.tail acceptedTail)

/-- The derived physical descent receipt supplies the head payload equation. -/
theorem walk_cons_receipt {budget : Nat} {combined : EqValue} {index : Nat}
    {value result : Value Symbol Guard} {values results : List (Value Symbol Guard)}
    {before middle after : Caller width} {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (head : NodeCall budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result middle)
    (tail : Walk budget combined (index + 1) values middle results after)
    (receipt : SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory before combined index)
    (headLaw : NodeLaw formulas solver ⟨(descend before combined index).1, value⟩ result)
    (tailLaw : WalkLaw formulas solver tail) : WalkLaw formulas solver (.cons head tail) :=
  walk_cons formulas solver head tail receipt.payload headLaw tailLaw

/-- Descended satisfaction makes an actual walk exact on its independent input forest. -/
theorem WalkLaw.exact {budget : Nat} {combined : EqValue} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    {actual : Walk budget combined index values before results after}
    (law : WalkLaw formulas solver actual) (ambient : Env Symbol) (terms : List (Term Symbol))
    (satisfied : DescendedSat combined index terms) :
    All₂ (meaning (holds formulas solver) ambient) results terms ↔
      All₂ (meaning (holds formulas solver) ambient) values terms :=
  ⟨law.narrows ambient terms, law.preserves ambient terms satisfied⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem erase_narrows (ambient : Env Symbol) (values : List (Value Symbol Guard)) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (holds formulas solver) ambient) (EqualityLeafProjectionRuntimeEmpty.erase values) terms) :
    All₂ (meaning (holds formulas solver) ambient) values terms := by
  induction values generalizing terms with
  | nil => exact accepted
  | cons value values ih =>
      cases accepted with
      | cons impossible _ => simp only [meaning] at impossible

/-- Contradiction erases slots and needs no recursive child law. -/
theorem children_contradiction (budget : Nat) (values : List (Value Symbol Guard)) (before : Caller width) :
    ChildrenLaw formulas solver (Children.contradiction (budget := budget) (values := values) (before := before)) :=
  ⟨fun ambient terms accepted => erase_narrows formulas solver ambient values terms accepted,
    fun _ _ _ impossible _ => False.elim impossible⟩

/-- A live parent supplies every offset required by the actual indexed walk. -/
theorem children_live {budget : Nat} {identity : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    (actual : Walk budget (.live identity records) 0 values before results after)
    (wellFormed : SourceEqualityDescend.WellFormed (SourceEqualityConstraintAllocation.Value.live identity records).payload)
    (law : WalkLaw formulas solver actual) : ChildrenLaw formulas solver (.live actual) :=
  ⟨law.narrows, fun ambient symbol terms satisfied accepted =>
    law.preserves ambient terms (SourceCurrentAllocatedPartialWalkLanguage.DescendedSat.of_parent _ wellFormed symbol terms satisfied) accepted⟩

/-- A satisfied combined parent makes its actual child branch exact. -/
theorem ChildrenLaw.exact {budget : Nat} {combined : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    {actual : Children budget combined values before results after}
    (law : ChildrenLaw formulas solver actual) (ambient : Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (satisfied : SourceEqualityPrecheck.Sat (.node symbol terms) combined.payload) :
    All₂ (meaning (holds formulas solver) ambient) results terms ↔
      All₂ (meaning (holds formulas solver) ambient) values terms :=
  ⟨law.narrows ambient terms, law.preserves ambient symbol terms satisfied⟩

end MicroCFTA.SourceCurrentAllocatedSharedPartialWalkLanguage
