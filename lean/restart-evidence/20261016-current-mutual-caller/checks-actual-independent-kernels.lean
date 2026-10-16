import MicroCFTA.SourceCurrentAllocatedPartialActual

namespace MicroCFTA.PartialActualIndependentKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialWalkLanguage (DescendedSat)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The exact-language root receipt and both result-family frames share the same actual return. -/
theorem root_exact_with_frames {inventory : Inventory} {identity : Nat} {value result : Node}
    {before after : Caller width} {memos final : Memos}
    {actual : NodeCall budget ⟨.live identity [], value⟩ before result after}
    (reads : NodeCallReads formulas solver actual memos final) (checks : Checks (nodeCallTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints (.live identity []))
    (available : Available before.checked.native.machine.heap value) :
    ∃ next, Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedPartialFrames.Frame before after ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨next, post, resident, language⟩ := SourceCurrentAllocatedPartialActual.root_exact formulas solver
    reads checks initial inherited available
  have frame := SourceCurrentAllocatedPartialFrames.node_call actual
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid initial.sound.valid)
  exact ⟨next, post, resident, frame, language⟩

/-- A second actual node call derives its current inventory/cache context from the first call. -/
theorem two_actual_calls {inventory : Inventory} {firstRequest secondRequest : NodeRequest}
    {before middle after : Caller width} {firstResult secondResult : Node} {memos middleMemos final : Memos}
    {first : NodeCall budget firstRequest before firstResult middle}
    {second : NodeCall budget secondRequest middle secondResult after}
    (firstReads : NodeCallReads formulas solver first memos middleMemos)
    (secondReads : NodeCallReads formulas solver second middleMemos final)
    (firstChecks : Checks (nodeCallTrace first)) (secondChecks : Checks (nodeCallTrace second))
    (initial : Context formulas solver inventory before memos)
    (firstInherited : EqReady before.checked.operations.constraints firstRequest.inherited)
    (secondInherited : EqReady before.checked.operations.constraints secondRequest.inherited)
    (firstAvailable : Available before.checked.native.machine.heap firstRequest.value)
    (secondAvailable : Available before.checked.native.machine.heap secondRequest.value) :
    ∃ next, Post formulas solver next before after final ∧
      Available after.checked.native.machine.heap firstResult ∧ Available after.checked.native.machine.heap secondResult ∧
      NodeLaw formulas solver firstRequest firstResult ∧ NodeLaw formulas solver secondRequest secondResult := by
  obtain ⟨middleInventory, firstPost, firstResident, firstLaw⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver
    firstReads inventory firstChecks initial firstInherited firstAvailable
  obtain ⟨next, secondPost, secondResident, secondLaw⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver
    secondReads middleInventory secondChecks firstPost.context
      (secondInherited.grows firstPost.effects.grows.constraint_growth)
      (firstPost.effects.keeps.available _ secondAvailable)
  exact ⟨next, firstPost.trans secondPost, secondPost.effects.keeps.available _ firstResident, secondResident,
    firstLaw, secondLaw⟩

/-- The completed actual walk derives its child laws and their exact conditional forest language. -/
theorem actual_walk_without_child_oracle {inventory : Inventory} {combined : EqValue} {index : Nat}
    {values results : List Node} {before after : Caller width} {memos final : Memos}
    {actual : Walk budget combined index values before results after}
    (reads : WalkReads formulas solver actual memos final) (checks : Checks (walkTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) :
    ∃ next, Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧
      results.length = values.length ∧
      ∀ ambient terms, DescendedSat combined index terms →
        (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
          All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) := by
  obtain ⟨next, post, resident, law⟩ := SourceCurrentAllocatedPartialActual.walk formulas solver
    reads inventory checks initial inherited available
  exact ⟨next, post, resident, actual.length, fun ambient terms satisfied => law.exact formulas solver ambient terms satisfied⟩

#print axioms root_exact_with_frames
#print axioms two_actual_calls
#print axioms actual_walk_without_child_oracle
set_option pp.explicit true
#check @root_exact_with_frames
#check @two_actual_calls
#check @actual_walk_without_child_oracle
end MicroCFTA.PartialActualIndependentKernels
