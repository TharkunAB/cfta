import MicroCFTA.SourceCurrentAllocatedPartialWalkLanguage

namespace MicroCFTA.PartialWalkLanguageKernels
open Cache Language InternedConstructorTemplates InternedGuardedLanguage
open SourceCurrentAllocatedPartialGraph (NodeCall Walk Children descend)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedPartialWalkLanguage
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "holds" => SourceEqualityPCSGuard.holds
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Two actual allocated requests compose at an arbitrary nonzero source offset. -/
theorem two_calls {budget index : Nat} {combined : EqValue}
    {first second firstResult secondResult : Value Symbol Guard} {before middle after : Caller width}
    (firstCall : NodeCall budget ⟨(descend before combined index).1, first⟩ (descend before combined index).2 firstResult middle)
    (secondCall : NodeCall budget ⟨(descend middle combined (index + 1)).1, second⟩
      (descend middle combined (index + 1)).2 secondResult after)
    (firstPayload : (descend before combined index).1.payload = SourceEqualityDescend.descend combined.payload index)
    (secondPayload : (descend middle combined (index + 1)).1.payload = SourceEqualityDescend.descend combined.payload (index + 1))
    (firstLaw : NodeLaw formulas solver ⟨(descend before combined index).1, first⟩ firstResult)
    (secondLaw : NodeLaw formulas solver ⟨(descend middle combined (index + 1)).1, second⟩ secondResult) :
    WalkLaw formulas solver (.cons firstCall (.cons secondCall (Walk.nil (combined := combined) (index := index + 1 + 1)))) := by
  exact walk_cons formulas solver firstCall _ firstPayload firstLaw
    (walk_cons formulas solver secondCall _ secondPayload secondLaw (walk_nil formulas solver budget combined _ after))

/-- Parent satisfaction supplies both literal offsets without a separate child-satisfaction premise. -/
theorem live_two_calls {budget identity : Nat} {records : List SourceEqualityClassOrder.Record}
    {first second firstResult secondResult : Value Symbol Guard} {before middle after : Caller width}
    (firstCall : NodeCall budget ⟨(descend before (.live identity records) 0).1, first⟩
      (descend before (.live identity records) 0).2 firstResult middle)
    (secondCall : NodeCall budget ⟨(descend middle (.live identity records) (0 + 1)).1, second⟩
      (descend middle (.live identity records) (0 + 1)).2 secondResult after)
    (firstPayload : (descend before (.live identity records) 0).1.payload = SourceEqualityDescend.descend (some records) 0)
    (secondPayload : (descend middle (.live identity records) (0 + 1)).1.payload = SourceEqualityDescend.descend (some records) (0 + 1))
    (firstLaw : NodeLaw formulas solver ⟨(descend before (.live identity records) 0).1, first⟩ firstResult)
    (secondLaw : NodeLaw formulas solver ⟨(descend middle (.live identity records) (0 + 1)).1, second⟩ secondResult)
    (wellFormed : SourceEqualityDescend.WellFormed (some records))
    (ambient : Env Symbol) (symbol : Symbol) (firstTerm secondTerm : Term Symbol)
    (satisfied : SourceEqualityPrecheck.Sat (.node symbol [firstTerm, secondTerm]) (some records)) :
    All₂ (meaning (holds formulas solver) ambient) [firstResult, secondResult] [firstTerm, secondTerm] ↔
      All₂ (meaning (holds formulas solver) ambient) [first, second] [firstTerm, secondTerm] := by
  have walked := two_calls formulas solver firstCall secondCall firstPayload secondPayload firstLaw secondLaw
  have children := children_live formulas solver _ wellFormed walked
  exact children.exact formulas solver ambient symbol _ satisfied

/-- Contradiction skips recursive calls and erases even a singleton input slot. -/
theorem contradiction_skips (budget : Nat) (value : Value Symbol Guard) (before : Caller width) :
    ∃ actual : Children budget .contradiction [value] before [.empty] before,
      ChildrenLaw formulas solver actual ∧
        ∀ ambient term, ¬ All₂ (meaning (holds formulas solver) ambient) [.empty] [term] := by
  refine ⟨.contradiction, children_contradiction formulas solver budget [value] before, ?_⟩
  intro ambient term accepted
  cases accepted with
  | cons impossible rest => simp only [meaning] at impossible

/-- A real descent receipt replaces a separate payload correspondence assumption. -/
theorem receipt_then_call {budget index : Nat} {combined : EqValue}
    {value result : Value Symbol Guard} {before after : Caller width}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (receipt : SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory before combined index)
    (actual : NodeCall budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result after)
    (law : NodeLaw formulas solver ⟨(descend before combined index).1, value⟩ result) :
    WalkLaw formulas solver (.cons actual (Walk.nil (combined := combined) (index := index + 1))) :=
  walk_cons_receipt formulas solver actual _ receipt law (walk_nil formulas solver budget combined (index + 1) after)

#print axioms two_calls
#print axioms live_two_calls
#print axioms contradiction_skips
#print axioms receipt_then_call
set_option pp.explicit true
#check @two_calls
#check @live_two_calls
#check @contradiction_skips
#check @receipt_then_call
end MicroCFTA.PartialWalkLanguageKernels
