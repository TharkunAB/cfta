import MicroCFTA.SourceCurrentAllocatedParentEdge

namespace MicroCFTA.WarmParentIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedParentEdge
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- Resident source edges derive their field load and child availability.
theorem resident_parent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (edge : EdgeValue Symbol Guard) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap edge)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : ∀ loaded, SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.operations.constraints = .ok (some loaded) →
      Ranges budget edge.entry.key.constraint loaded inherited edge.children before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ loaded result after savedFourth saved next final,
      ∃ actual : Edge budget edge.entry.key.symbol edge.entry.key.constraint loaded inherited edge.children before fourth memo
        result after savedFourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next edge.entry.key.symbol edge.entry.key.constraint loaded inherited edge.children before
        result after fourth savedFourth memo saved final := by
  obtain ⟨cached, loaded, found⟩ := ready.good.fields edge.entry.key edge resident
  have available := ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  obtain ⟨result, after, savedFourth, saved, next, final, actual, reads, receipt⟩ := finite
    formulas solver inventory budget edge.entry.key.symbol edge.entry.key.constraint loaded inherited edge.children
    before fourth memo ready admitted cached found inheritedReady available correct stored covered (ranges loaded found) memos valid
  exact ⟨loaded, result, after, savedFourth, saved, next, final, actual, reads, receipt⟩

-- A second source edge uses the first edge's literal state and all returned memo families.
theorem two_warm_edges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (first second : EdgeValue Symbol Guard) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (firstResident : InternedEdgeResidency.EdgeResident before.native.machine.heap first)
    (secondResident : InternedEdgeResidency.EdgeResident before.native.machine.heap second)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (firstRanges : ∀ loaded, SourceEqualityConstraintFieldLookup.load first.entry.key.constraint before.operations.constraints = .ok (some loaded) →
      Ranges budget first.entry.key.constraint loaded inherited first.children before fourth memo)
    (secondRanges : ∀ loaded result middle savedFourth saved,
      Edge budget first.entry.key.symbol first.entry.key.constraint loaded inherited first.children before fourth memo result middle savedFourth saved →
      ∀ nextLoaded, SourceEqualityConstraintFieldLookup.load second.entry.key.constraint middle.operations.constraints = .ok (some nextLoaded) →
        Ranges budget second.entry.key.constraint nextLoaded inherited second.children middle savedFourth saved)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ firstLoaded firstResult middle middleFourth middleMerge middleInventory middleGlobals
      secondLoaded secondResult after savedFourth saved next final,
      Receipt formulas solver middleInventory first.entry.key.symbol first.entry.key.constraint firstLoaded inherited first.children
        before firstResult middle fourth middleFourth memo middleMerge middleGlobals ∧
      Receipt formulas solver next second.entry.key.symbol second.entry.key.constraint secondLoaded inherited second.children
        middle secondResult after middleFourth savedFourth middleMerge saved final ∧
      Extends memo saved ∧ SourceCurrentEmptinessMemo.Extends fourth savedFourth ∧
      Valid after.native.machine.heap final := by
  obtain ⟨firstLoaded, firstResult, middle, middleFourth, middleMerge, middleInventory, middleGlobals, firstActual, _, firstReceipt⟩ :=
    resident_parent formulas solver inventory budget first inherited before fourth memo ready admitted firstResident inheritedReady
      correct stored covered firstRanges memos valid
  have secondResident := InternedEdgeResidency.edge_grows before.native.machine.heap middle.native.machine.heap
    firstReceipt.effects.keeps.growth second secondResident
  obtain ⟨secondLoaded, secondResult, after, savedFourth, saved, next, final, _, _, secondReceipt⟩ :=
    resident_parent formulas solver middleInventory budget second inherited middle middleFourth middleMerge
      firstReceipt.ready firstReceipt.admitted secondResident (inheritedReady.grows firstReceipt.effects.grows.constraint_growth)
      firstReceipt.correct firstReceipt.stored firstReceipt.covered
      (secondRanges firstLoaded firstResult middle middleFourth middleMerge firstActual) middleGlobals firstReceipt.globals
  exact ⟨firstLoaded, firstResult, middle, middleFourth, middleMerge, middleInventory, middleGlobals,
    secondLoaded, secondResult, after, savedFourth, saved, next, final, firstReceipt, secondReceipt,
    extends_trans firstReceipt.retained secondReceipt.retained,
    fun key entry found => secondReceipt.fourthRetained key entry (firstReceipt.fourthRetained key entry found),
    secondReceipt.globals⟩

end MicroCFTA.WarmParentIntegration

#print axioms MicroCFTA.WarmParentIntegration.resident_parent
#print axioms MicroCFTA.WarmParentIntegration.two_warm_edges
#check @MicroCFTA.WarmParentIntegration.resident_parent
#check @MicroCFTA.WarmParentIntegration.two_warm_edges
