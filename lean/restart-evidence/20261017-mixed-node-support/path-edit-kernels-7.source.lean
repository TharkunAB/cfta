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
    .unselected 0 (by rfl) .nil
  have reads : ChildrenReads formulas solver base actual memos memos := .unselected (absent := rfl) .nil
  have leaves : ChildrenLeaves valid actual := by
    intro event reached
    cases reached with
    | unselected impossible => cases impossible
    | selected_first _ => simp_all [SourceEqualityNeededMap.lookup]
    | selected_rest _ => simp_all [SourceEqualityNeededMap.lookup]
  have populated : Populated (.editBelow [(-1, .editAt token)]) := by
    rw [Populated]
    intro index child found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp found)
    exact ⟨True.intro, ⟨[], token, by simp [SourceEqualityEditLeafPaths.leaves]⟩⟩
  have allowed : SourceEqualitySharedEditEffects.Allowed record (.editBelow [(-1, .editAt token)]) := by
    rw [SourceEqualitySharedEditEffects.Allowed, SourceEqualityEdits.All]
    intro index child found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp found)
    exact member
  have safe : ChildrenSafe [(-1, .editAt token)] 0 [value] := by
    intro query child found
    have different : Int.ofNat (0 + query) ≠ -1 := by
      change ((0 + query : Nat) : Int) ≠ -1
      omega
    simp only [SourceEqualityNeededMap.lookup, different, ite_false] at found
    cases found
  have placed : ChildrenAtLeaves valid [(-1, .editAt token)] 0 [value] := by
    intro query child found
    have different : Int.ofNat (0 + query) ≠ -1 := by
      change ((0 + query : Nat) : Int) ≠ -1
      omega
    simp only [SourceEqualityNeededMap.lookup, different, ite_false] at found
    cases found
  have produced := children_with_leaf_certificates valid reads leaves inventory depth populated allowed ready
    (fun child present => (List.mem_singleton.mp present) ▸ available) safe global stored
    (fun child present => (List.mem_singleton.mp present) ▸ bounded) placed
  exact ⟨actual, reads, produced⟩

/-- Two actual constructor requests retain the nullary row's arbitrary raw guard and all input masks. -/
theorem nullary_rebuild [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
    (before : SharedState width)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edge : EdgeValue Symbol Guard)
    (level : Nat) (free : List InternedBinderProtocol.Reference) (noChildren : edge.children = [])
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap (.node entry [edge] level free))
    (stored : MuStored valid before.checked.native.machine.heap) :
    ∃ rebuilt middle result heap,
      run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint []) before.checked.native.machine.heap = (rebuilt, middle) ∧
      run (InternedConstructorTemplates.makeNode [rebuilt]) middle = (result, heap) ∧
      RowPreserves valid edge rebuilt ∧ MuStored valid heap ∧ Preserves valid (.node entry [edge] level free) result := by
  let edgeBuilt := run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint []) before.checked.native.machine.heap
  let middle := advanceHeap before edgeBuilt.2
  let nodeBuilt := run (InternedConstructorTemplates.makeNode [edgeBuilt.1]) edgeBuilt.2
  have facts := ready.checked.semantic.ready.semantic.1.normal.facts
  have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
  have field := ready.checked.good.fields _ _ (resident edge List.mem_cons_self)
  have nilAvailable : Values before.checked.native.machine.heap [] := by intro value member; cases member
  have physical := SourceCurrentAllocatedSharedEditEffects.edge_physical ready edge.entry.key.symbol edge.entry.key.constraint [] field nilAvailable
  have edgeReady : Ready formulas solver inventory record originals base middle := physical.1
  have currentFacts := edgeReady.checked.semantic.ready.semantic.1.normal.facts
  have relation := SourceCurrentConstrainedCapEditSupport.makeEdge valid edge [] before.checked.native.machine.heap
    facts.coherent facts.cached nilAvailable (by rw [noChildren]; exact .nil)
  have edges : InternedNestedProvenance.Edges edgeBuilt.2 [edgeBuilt.1] := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact physical.2.2.1
  have narrowed := SourceCurrentConstrainedCapEditSupport.makeNode valid entry [edge] [edgeBuilt.1] level free edgeBuilt.2
    currentFacts.coherent currentFacts.linked edges (.cons relation .nil)
  have edgeStore := stored.makeEdge edge.entry.key.symbol edge.entry.key.constraint []
  have nodeStore := edgeStore.makeNode [edgeBuilt.1]
  exact ⟨edgeBuilt.1, edgeBuilt.2, nodeBuilt.1, nodeBuilt.2, rfl, rfl, relation, nodeStore, narrowed⟩

end MicroCFTA.PathEditChecks

#print axioms MicroCFTA.PathEditChecks.own_head
#check @MicroCFTA.PathEditChecks.own_head
#print axioms MicroCFTA.PathEditChecks.negative_slot
#check @MicroCFTA.PathEditChecks.negative_slot
#print axioms MicroCFTA.PathEditChecks.nullary_rebuild
#check @MicroCFTA.PathEditChecks.nullary_rebuild
