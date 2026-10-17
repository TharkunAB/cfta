import MicroCFTA.SourceCurrentConstrainedCapEditSupport

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.PathEditChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityAnnotationLanguage SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceCurrentConstrainedCapPaths SourceCurrentConstrainedCapEditSupport
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentEditDomains
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory

/-- This kernel constructs its own recursive head before it transports a short initial edit mask. -/
theorem own_head [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    (value : Value Symbol Guard) (before : Heap) (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (stored : MuStored valid before) (bounded : SourceCurrentConstrainedCap.Cap valid depth value)
    (edits : Edits EqualityNormalize.Path) (placed : AtLeaves valid edits value) :
    ∃ result after, SourceEqualityRequiredHead.Head value before result after ∧
      MuStored valid after ∧ Preserves valid value result ∧ AtLeaves valid edits result := by
  obtain ⟨result, after, actual, _⟩ := SourceEqualityRequiredHead.complete value before ready available closed
  have produced := SourceCurrentConstrainedCapEditSupport.head valid depth actual ready available closed bounded stored
  exact ⟨result, after, actual, produced.1, produced.2, placement_preserved produced.2 placed⟩

/-- A negative stored edit slot does not select the first original value. -/
theorem negative_slot [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
    (state : SharedState width) (token : EqualityNormalize.Path) (member : token ∈ record.paths)
    (value : Value Symbol Guard) (depth : Nat)
    (ready : Ready formulas solver inventory record originals base state)
    (available : Available state.checked.native.machine.heap value)
    (memos : Memos) (global : EndpointMemoGateTrace.Valid state.checked.native.machine.heap memos)
    (stored : MuStored valid state.checked.native.machine.heap) (bounded : SourceCurrentConstrainedCap.Cap valid depth value) :
    ∃ actual : EditChildren record originals [(-1, .editAt token)] 0 [value] state [value] state,
      ChildrenReads formulas solver base actual memos memos ∧
      MuStored valid state.checked.native.machine.heap ∧ All₂ (Preserves valid) [value] [value] := by
  let actual : EditChildren record originals [(-1, .editAt token)] 0 [value] state [value] state :=
    .unselected 0 (by simp only [SourceEqualityNeededMap.lookup]; decide) .nil
  have reads : ChildrenReads formulas solver base actual memos memos := .unselected .nil
  have leaves : ChildrenLeaves valid actual := by
    intro event reached
    cases reached with
    | unselected impossible => cases impossible
  have populated : Populated (.editBelow [(-1, .editAt token)]) := by
    intro index child found
    obtain rfl := List.mem_singleton.mp found
    exact ⟨True.intro, ⟨[], token, by simp [leaves]⟩⟩
  have allowed : SourceEqualitySharedEditEffects.Allowed record (.editBelow [(-1, .editAt token)]) := by
    intro index child found
    obtain rfl := List.mem_singleton.mp found
    exact member
  have safe : ChildrenSafe [(-1, .editAt token)] 0 [value] := by
    intro query child found
    simp only [SourceEqualityNeededMap.lookup] at found
    split at found
    · rename_i same
      omega
    · cases found
  have placed : ChildrenAtLeaves valid [(-1, .editAt token)] 0 [value] := by
    intro query child found
    simp only [SourceEqualityNeededMap.lookup] at found
    split at found
    · rename_i same
      omega
    · cases found
  have produced := children_with_leaf_certificates valid reads leaves inventory depth populated allowed ready
    (fun child present => (List.mem_singleton.mp present) ▸ available) safe global stored
    (fun child present => (List.mem_singleton.mp present) ▸ bounded) placed
  exact ⟨actual, reads, produced⟩

/-- The actual row and node rebuild retain arbitrary raw guards when selected slots are missing. -/
theorem nullary_rebuild [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
    (before : SharedState width) (token : EqualityNormalize.Path) (member : token ∈ record.paths)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edge : EdgeValue Symbol Guard)
    (level : Nat) (free : List InternedBinderProtocol.Reference) (noChildren : edge.children = [])
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap (.node entry [edge] level free))
    (memos : Memos) (global : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (stored : MuStored valid before.checked.native.machine.heap) :
    ∃ result after, ∃ actual : EditNode record originals (.editBelow [(0, .editAt token)]) (.node entry [edge] level free) before result after,
      NodeReads formulas solver base actual memos memos ∧
      MuStored valid after.checked.native.machine.heap ∧ Preserves valid (.node entry [edge] level free) result := by
  let entries : List (Int × Edits EqualityNormalize.Path) := [(0, .editAt token)]
  let edgeBuilt := run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint []) before.checked.native.machine.heap
  let middle := advanceHeap before edgeBuilt.2
  let nodeBuilt := run (InternedConstructorTemplates.makeNode [edgeBuilt.1]) middle.checked.native.machine.heap
  let after := advanceHeap middle nodeBuilt.2
  have children : EditChildren record originals entries 0 edge.children before [] before := by rw [noChildren]; exact .nil
  have childReads : ChildrenReads formulas solver base children memos memos := by
    simpa only [noChildren] using (show ChildrenReads formulas solver base
      (.nil (record := record) (originals := originals) (entries := entries) (index := 0) (state := before)) memos memos from .nil)
  let rows : EditRows record originals entries [edge] before [edgeBuilt.1] middle := .cons children rfl .nil
  have rowReads : RowsReads formulas solver base rows memos memos := .cons childReads .nil
  let actual : EditNode record originals (.editBelow entries) (.node entry [edge] level free) before nodeBuilt.1 after := .ordinary rows rfl
  have reads : NodeReads formulas solver base actual memos memos := .ordinary rowReads
  have leafChecks : NodeLeaves valid actual := by
    intro event reached
    cases reached with
    | ordinary inside =>
        cases inside with
        | first child =>
            have emptyChildren : ChildrenLeaf event (.nil (record := record) (originals := originals) (entries := entries) (index := 0) (state := before)) := by
              simpa only [noChildren] using child
            cases emptyChildren
        | rest impossible => cases impossible
  have populated : Populated (.editBelow entries) := by
    intro index child found
    obtain rfl := List.mem_singleton.mp found
    exact ⟨True.intro, ⟨[], token, by simp [SourceEqualityEditLeafPaths.leaves]⟩⟩
  have nonempty : HasLeaf (.editBelow entries) := ⟨[0], token, by simp [entries, SourceEqualityEditLeafPaths.leaves]⟩
  have allowed : SourceEqualitySharedEditEffects.Allowed record (.editBelow entries) := by
    intro index child found
    obtain rfl := List.mem_singleton.mp found
    exact member
  have rowSafe : RowsSafe entries [edge] := by
    intro row present query child found value selected
    obtain rfl := List.mem_singleton.mp present
    rw [noChildren] at selected
    cases selected
  have safe : Safe (.editBelow entries) (.node entry [edge] level free : Value Symbol Guard) := by
    intro path action retained
    have same : path = [0] := by simpa [entries, SourceEqualityEditLeafPaths.leaves] using congrArg Prod.fst (List.mem_singleton.mp retained)
    subst path
    intro row present child selected
    obtain rfl := List.mem_singleton.mp present
    simp [noChildren, SourceEqualityProjectionGraph.select] at selected
  have bounded : SourceCurrentConstrainedCap.Cap valid 1 (.node entry [edge] level free) := by
    apply SourceCurrentConstrainedCap.Cap.node
    intro child present
    simp [noChildren] at present
  have placed : AtLeaves valid (.editBelow entries) (.node entry [edge] level free : Value Symbol Guard) := by
    intro path action retained
    have same : path = [0] := by simpa [entries, SourceEqualityEditLeafPaths.leaves] using congrArg Prod.fst (List.mem_singleton.mp retained)
    subst path
    apply Supported.node
    intro row present child selected
    obtain rfl := List.mem_singleton.mp present
    simp [noChildren, SourceEqualityProjectionGraph.select] at selected
  have produced := node_with_leaf_certificates valid reads leafChecks inventory 1 populated nonempty allowed ready available safe global stored bounded placed
  exact ⟨nodeBuilt.1, after, actual, reads, produced⟩

end MicroCFTA.PathEditChecks

#print axioms MicroCFTA.PathEditChecks.own_head
#check @MicroCFTA.PathEditChecks.own_head
#print axioms MicroCFTA.PathEditChecks.negative_slot
#check @MicroCFTA.PathEditChecks.negative_slot
#print axioms MicroCFTA.PathEditChecks.nullary_rebuild
#check @MicroCFTA.PathEditChecks.nullary_rebuild
