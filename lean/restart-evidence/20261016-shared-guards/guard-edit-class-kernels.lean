import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardClassPass
import MicroCFTA.SourceCurrentAllocatedSharedEditComplete
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts

namespace MicroCFTA.GuardEditIntegrationChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
local notation "Guards" => SourceCurrentAllocatedFiniteOrdinaryGuardShared.Stored
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Profile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "NodeProfile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "LeafLimit" => SourceCurrentAllocatedFiniteOrdinaryGuardIteration.leafLimit
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem two_selected_count {record originals path first second before results after}
    (actual : EditChildren (width := width) record originals [(0, .editAt path), (1, .editAt path)] 0 [first, second] before results after) :
    ChildrenCount actual 2 := by
  cases actual with
  | unselected _ absent _ => simp [SourceEqualityNeededMap.lookup] at absent
  | selected _ found first rest =>
      simp [SourceEqualityNeededMap.lookup] at found
      cases found
      cases first with
      | leaf one =>
          cases rest with
          | unselected _ absent _ => simp [SourceEqualityNeededMap.lookup] at absent
          | selected _ found second rest =>
              simp [SourceEqualityNeededMap.lookup] at found
              cases found
              cases second with
              | leaf two =>
                  cases rest with
                  | nil => exact .selected (found := rfl) (.leaf one) (.selected (found := rfl) (.leaf two) .nil)

section Initial
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
variable (base : InternedConstructorTemplates.State Symbol Guard) (before : Shared width)
variable (known : Values base originals) (coherent : SourceEqualityClassOrder.Coherent record)
variable (active : EqualityNormalize.Nontrivial record.paths) (inventory : Inventory)
variable (ready : Ready formulas solver inventory record originals base before)
variable (stored : Stored before) (guards : Guards record originals before)
variable (capturedLimits inputLimits : Limits) (capturedProfile : Profile capturedLimits originals)
variable (path : EqualityNormalize.Path) (member : path ∈ record.paths)
variable (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
include known coherent active ready stored guards capturedProfile member valid

/-- A constructed Empty callback derives its own same-return guard profile and retains every causal slot law. -/
theorem constructed_empty_leaf
    (ranges : SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals path .empty before) :
    ∃ result after next final, ∃ actual : EditNode record originals (.editAt path) .empty before result after,
      NodeReads formulas solver base actual memos final ∧ NodeCount actual 1 ∧
      SourceCurrentAllocatedSharedEditEffects.NodeReceipt formulas solver next record originals base .empty before result after memos final ∧
      Guards record originals after ∧ NodeProfile (LeafLimit record capturedLimits inputLimits) result := by
  have capturedDomain := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.domain originals capturedProfile
  have domains : ∀ selected ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (selected.map Int.ofNat) originals :=
    fun selected _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.checked.semantic originals
      (fun value present => ready.captured.available value (known value present)) capturedDomain _
  have safe : Safe (.editAt path) (.empty : Value Symbol Guard) :=
    closed_safe _ _ _ ready.checked.semantic (empty_available _) rfl
  have populated : Populated (.editAt path) := by simp only [Populated]
  have nonempty : HasLeaf (.editAt path) := ⟨[], path, by simp [leaves]⟩
  have allowed : Allowed record (.editAt path) := by simpa only [Allowed, All] using member
  obtain ⟨result, after, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedSharedEditComplete.node_complete formulas solver record originals base known domains coherent active
      inventory (.leaf ranges) populated nonempty allowed ready (empty_available _) safe memos valid
  have own := SourceCurrentAllocatedFiniteOrdinaryGuardEdit.node reads populated nonempty allowed ready
    (empty_available _) safe valid known capturedDomain stored .empty guards capturedLimits inputLimits capturedProfile trivial
  have counted : NodeCount actual 1 := by cases actual with | leaf leaf => exact .leaf leaf
  exact ⟨result, after, next, final, actual, reads, counted, receipt, own⟩

/-- Two repeated Empty positions produce two callbacks but retain one common original-input envelope. -/
theorem constructed_two_empty_leaves
    (ranges : SourceCurrentAllocatedSharedEditRanges.ChildrenRanges record originals
      [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) before) :
    ∃ results after next final,
      ∃ actual : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 0
          ([.empty, .empty] : List (Value Symbol Guard)) before results after,
        ChildrenReads formulas solver base actual memos final ∧ ChildrenCount actual 2 ∧
        SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record originals base
          ([.empty, .empty] : List (Value Symbol Guard)) before results after memos final ∧
        Guards record originals after ∧ Profile (LeafLimit record capturedLimits inputLimits) results := by
  have capturedDomain := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.domain originals capturedProfile
  have domains : ∀ selected ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (selected.map Int.ofNat) originals :=
    fun selected _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.checked.semantic originals
      (fun value present => ready.captured.available value (known value present)) capturedDomain _
  have populated : Populated (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Populated]
    intro index child included
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at included
    rcases included with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by simp only [Populated], [], path, by simp [leaves]⟩
  have allowed : Allowed record (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Allowed, All]
    intro index child included
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at included
    rcases included with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa only [All] using member
  have available : Values before.checked.native.machine.heap ([.empty, .empty] : List (Value Symbol Guard)) := by
    intro value selected
    have same : value = .empty := by simpa using selected
    exact same ▸ empty_available _
  have safe : ChildrenSafe [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) := by
    intro query child found value selected
    have same : value = .empty := by
      have present := List.mem_of_getElem? selected
      simpa using present
    subst value
    exact closed_safe _ _ _ ready.checked.semantic (empty_available _) rfl
  obtain ⟨results, after, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedSharedEditComplete.children_complete formulas solver record originals base known domains coherent active
      inventory ranges populated allowed ready available safe memos valid
  have own := SourceCurrentAllocatedFiniteOrdinaryGuardEdit.children reads populated allowed ready available safe valid
    known capturedDomain stored (.cons .empty (.cons .empty .nil)) guards capturedLimits inputLimits capturedProfile
      (show Profile inputLimits ([.empty, .empty] : List (Value Symbol Guard)) from ⟨trivial, trivial, trivial⟩)
  exact ⟨results, after, next, final, actual, reads, two_selected_count actual, receipt, own⟩
end Initial

/-- Initial ranges construct the same full class pass, then the literal class step sum bounds its actual output guards. -/
theorem constructed_pass
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : SourceEqualityNativeDemand.State width) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native)
    (merged : SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored memo)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored before.native)
    (mergeGuards : SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored memo)
    (limits : Limits) (profile : Profile limits values) (count : Nat)
    (enough : SourceCurrentAllocatedFiniteOrdinaryGuardOwn.classSteps records ≤ count)
    (ranges : SourceCurrentAllocatedClassPass.Ranges records values before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final,
      ∃ actual : SourceCurrentAllocatedClassPass.Pass records values before memo results after saved,
        SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final ∧
        SourceCurrentAllocatedClassPass.Receipt formulas solver next records values before memo results after saved memos final ∧
        SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored saved ∧
        SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored after.native ∧
        Profile (SourceCurrentAllocatedFiniteOrdinaryGuardTarget.foldLimit limits count) results := by
  have domain := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.domain values profile
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, _native, _merged, _narrow⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryClassPass.finite formulas solver inventory ranges coherent active ready admitted
      available domain physical covered native merged memos valid
  have own := SourceCurrentAllocatedFiniteOrdinaryGuardClassPass.pass formulas solver inventory reads coherent active ready admitted
    available domain physical covered native merged valid guards mergeGuards limits profile
  exact ⟨results, after, saved, next, final, actual, reads, receipt, own.1, own.2.1,
    SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.mono _ own.2.2
      (SourceCurrentAllocatedFiniteOrdinaryGuardClassPass.passLimit_le_count limits records count enough)⟩

end MicroCFTA.GuardEditIntegrationChecks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.GuardEditIntegrationChecks.constructed_empty_leaf
#check @MicroCFTA.GuardEditIntegrationChecks.constructed_empty_leaf

#print axioms MicroCFTA.GuardEditIntegrationChecks.constructed_two_empty_leaves
#check @MicroCFTA.GuardEditIntegrationChecks.constructed_two_empty_leaves

#print axioms MicroCFTA.GuardEditIntegrationChecks.constructed_pass
#check @MicroCFTA.GuardEditIntegrationChecks.constructed_pass
