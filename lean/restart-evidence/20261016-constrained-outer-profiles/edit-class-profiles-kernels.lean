import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPassProfiles

namespace MicroCFTA.EditClassProfilesIndependent
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "SharedStored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}

/-- Empty below-edits construct the exact unchanged read graph without a leaf query. -/
theorem empty_below
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {base : Heap} {entries : List (Int × Edits EqualityNormalize.Path)} {before : SharedState width} {memos : Memos}
    (populated : Populated (.editBelow entries)) (nonempty : HasLeaf (.editBelow entries))
    (allowed : Allowed record (.editBelow entries)) (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap (.empty : Value Symbol Guard))
    (safe : Safe (.editBelow entries) (.empty : Value Symbol Guard)) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedDomain : DChildren originals) (stored : SharedStored before)
    (profiles : Profiles before.memo) (output : OutputStored before.checked.native) :
    ∃ actual : EditNode record originals (.editBelow entries) (.empty : Value Symbol Guard) before .empty before,
      NodeReads formulas solver base actual memos memos ∧ Profiles before.memo ∧ OutputStored before.checked.native := by
  let actual : EditNode record originals (.editBelow entries) (.empty : Value Symbol Guard) before .empty before := .empty
  have reads : NodeReads formulas solver base actual memos memos := .empty
  exact ⟨actual, reads, SourceCurrentAllocatedFiniteOrdinaryEditProfiles.node reads populated nonempty allowed ready
    available safe valid known capturedDomain stored .empty profiles output⟩

/-- Child-list root leaves are ignored at the exact full shared state. -/
theorem root_list_leaf
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {originals values : List (Value Symbol Guard)}
    {base : Heap} {path : EqualityNormalize.Path} {before : SharedState width} {memos : Memos}
    (allowed : Allowed record (.editAt path)) (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedDomain : DChildren originals) (stored : SharedStored before) (domain : DChildren values)
    (profiles : Profiles before.memo) (output : OutputStored before.checked.native) :
    ∃ actual : EditList record originals (.editAt path) values before values before,
      ListReads formulas solver base actual memos memos ∧ Profiles before.memo ∧ OutputStored before.checked.native := by
  let actual : EditList record originals (.editAt path) values before values before := .leaf
  have reads : ListReads formulas solver base actual memos memos := .leaf
  exact ⟨actual, reads, SourceCurrentAllocatedFiniteOrdinaryEditProfiles.list reads (by simp only [Populated]) allowed ready available
    (by trivial) valid known capturedDomain stored domain profiles output⟩

/-- Two concrete leaf receipts build selected child reads in their actual state order. -/
theorem selected_two
    {inventory firstInventory secondInventory : Inventory} {record : SourceEqualityClassOrder.Record}
    {originals : List (Value Symbol Guard)} {base : Heap}
    {entries : List (Int × Edits EqualityNormalize.Path)} {firstPath secondPath : EqualityNormalize.Path}
    {firstInput secondInput firstResult secondResult : Value Symbol Guard}
    {before middle after : SharedState width} {memos current final : Memos}
    (one : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver firstInventory record originals base firstPath
      firstInput before firstResult middle memos current)
    (two : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver secondInventory record originals base secondPath
      secondInput middle secondResult after current final)
    (found0 : SourceEqualityNeededMap.lookup (0 : Int) entries = some (.editAt firstPath))
    (found1 : SourceEqualityNeededMap.lookup (1 : Int) entries = some (.editAt secondPath))
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap [firstInput, secondInput])
    (safe : ChildrenSafe entries 0 [firstInput, secondInput]) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedDomain : DChildren originals) (stored : SharedStored before)
    (domain : DChildren [firstInput, secondInput])
    (profiles : Profiles before.memo) (output : OutputStored before.checked.native) :
    ∃ actual : EditChildren record originals entries 0 [firstInput, secondInput] before [firstResult, secondResult] after,
      ChildrenReads formulas solver base actual memos final ∧ Profiles after.memo ∧ OutputStored after.checked.native := by
  let nodeOne := EditNode.leaf one.actual
  let nodeTwo := EditNode.leaf two.actual
  let endGraph : EditChildren record originals entries 2 [] after [] after := .nil
  let tailGraph := EditChildren.selected 1 found1 nodeTwo endGraph
  let actual := EditChildren.selected 0 found0 nodeOne tailGraph
  have reads : ChildrenReads formulas solver base actual memos final :=
    .selected (first := nodeOne) (rest := tailGraph) (found := found0) (.leaf one)
      (.selected (first := nodeTwo) (rest := endGraph) (found := found1) (.leaf two) .nil)
  exact ⟨actual, reads, SourceCurrentAllocatedFiniteOrdinaryEditProfiles.children reads populated allowed ready
    available safe valid known capturedDomain stored domain profiles output⟩

/-- A complete two-class pass joins semantic and strong profile facts at the same tail-first return. -/
theorem two_class_pass
    {inventory : Inventory} {headRecord tailRecord : SourceEqualityClassOrder.Record}
    {values middle results : List (Value Symbol Guard)} {before next after : Checked width} {memo current saved : Memo}
    {memos stepMemos final : Memos}
    {tailClass : SourceCurrentAllocatedClassEdits.Class tailRecord values before memo middle next current}
    {headClass : SourceCurrentAllocatedClassEdits.Class headRecord middle next current results after saved}
    (tailReads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver tailClass memos stepMemos)
    (headReads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver headClass stepMemos final)
    (coherent : ∀ record ∈ [headRecord, tailRecord], SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ [headRecord, tailRecord], EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native) (profiles : Profiles memo)
    (valid : Valid before.native.machine.heap memos) (output : OutputStored before.native) :
    ∃ actual : SourceCurrentAllocatedClassPass.Pass [headRecord, tailRecord] values before memo
      (EqualityLeafProjectionRuntimeEmpty.propagate results) after saved,
      SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final ∧
      ∃ nextInventory, SourceCurrentAllocatedClassPass.Receipt formulas solver nextInventory [headRecord, tailRecord] values
        before memo (EqualityLeafProjectionRuntimeEmpty.propagate results) after saved memos final ∧
        Profiles saved ∧ OutputStored after.native ∧
        All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.propagate results) := by
  let tail : SourceCurrentAllocatedClassPass.Fold [tailRecord] values before memo middle next current := .cons .nil tailClass
  let both : SourceCurrentAllocatedClassPass.Fold [headRecord, tailRecord] values before memo results after saved := .cons tail headClass
  let actual := SourceCurrentAllocatedClassPass.Pass.done both
  have reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final :=
    .done (.cons (tail := tail) (head := headClass) (.cons (tail := .nil) (head := tailClass) .nil tailReads) headReads)
  have retained := SourceCurrentAllocatedFiniteOrdinaryClassPassProfiles.pass formulas solver inventory reads coherent active
    ready admitted available domain physical covered native profiles valid output
  obtain ⟨nextInventory, receipt, _, _, relation⟩ := SourceCurrentAllocatedFiniteOrdinaryClassPass.pass formulas solver inventory
    reads coherent active ready admitted available domain physical covered native profiles.domain valid
  exact ⟨actual, reads, nextInventory, receipt, retained.1, retained.2, relation⟩

end MicroCFTA.EditClassProfilesIndependent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.EditClassProfilesIndependent.empty_below
#check @MicroCFTA.EditClassProfilesIndependent.empty_below
#print axioms MicroCFTA.EditClassProfilesIndependent.root_list_leaf
#check @MicroCFTA.EditClassProfilesIndependent.root_list_leaf
#print axioms MicroCFTA.EditClassProfilesIndependent.selected_two
#check @MicroCFTA.EditClassProfilesIndependent.selected_two
#print axioms MicroCFTA.EditClassProfilesIndependent.two_class_pass
#check @MicroCFTA.EditClassProfilesIndependent.two_class_pass
