import MicroCFTA.SourceCurrentRequiredGuardOrigins
import MicroCFTA.SourceCurrentSharedEditRowLineage
import MicroCFTA.SourceEqualityClassFoldGraph

/-!
# Unselected child positions in actual Required and Edit rows

These statements concern completed call graphs. They preserve literal child
values at absent map keys. Other child positions can use arbitrary recursive
calls. Node normalization can remove or reorder rows.
-/
namespace MicroCFTA.SourceCurrentPositionalRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- An absent Required child key retains the complete value at that position. -/
theorem required_children {entries : List (Int × Needed)} {offset : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries offset values before results after) (index : Nat)
    (absent : SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = none) :
    results[index]? = values[index]? := by
  induction index generalizing offset values results before after with
  | zero =>
      cases actual with
      | nil => rfl
      | unselected => rfl
      | selected index found => simp only [Nat.add_zero] at absent; rw [found] at absent; contradiction
  | succ index ih =>
      cases actual with
      | nil => rfl
      | unselected offset _ rest =>
          exact ih rest (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using absent)
      | selected offset _ _ rest =>
          exact ih rest (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using absent)

/-- A surviving Required row retains an indexed original row and its unselected child. -/
theorem required_rows {entries : List (Int × Needed)} {originals results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireRows entries originals before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before originals)
    (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    ∀ result ∈ results, ∃ sourceIndex original, originals[sourceIndex]? = some original ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original result ∧ result.children[index]? = original.children[index]? := by
  have origin : ∀ result ∈ results, ∃ original ∈ originals,
      SourceCurrentRequiredGuardOrigins.RowOrigin original result ∧ result.children[index]? = original.children[index]? := by
    induction originals generalizing results before after with
    | nil => cases actual; intro result member; cases member
    | cons edge edges ih =>
        have tailResident : Edges before edges := fun row member => resident row (List.mem_cons_of_mem _ member)
        cases actual with
        | rejected rejected rest =>
            intro result member
            obtain ⟨original, included, kept⟩ := ih rest semantic costs tailResident result member
            exact ⟨original, List.mem_cons_of_mem _ included, kept⟩
        | @kept _ _ values middle result afterEdge _ _ _ _ fits children built rest =>
            have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
              edge.entry.key edge (resident edge List.mem_cons_self)
            have childEffects := SourceCurrentRequiredHeapEffects.children (fun _ => True) children semantic costs
              (fun _ _ _ => trivial) available
            have fields := MergedPhysicalGroupEdges.makeEdge_fields middle childEffects.2.1.ready.semantic.1.normal.facts
              edge.entry.key.symbol edge.entry.key.constraint values childEffects.2.2.2.2
            have equalChildren : result.children = values := by simpa only [built] using fields.2.2
            have firstOrigin : SourceCurrentRequiredGuardOrigins.RowOrigin edge result :=
              ⟨by simpa only [built] using fields.2.1, by simpa only [built] using fields.1,
                (congrArg List.length equalChildren).trans children.length⟩
            have unchanged : result.children[index]? = edge.children[index]? := by
              rw [equalChildren]
              exact required_children children index (by simpa only [Nat.zero_add] using absent)
            have edgeEffects := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint
              values middle childEffects.2.1.ready childEffects.2.2.2.2
            have afterKept : SourceEqualityRequiredCache.Keeps middle afterEdge := by simpa only [built] using edgeEffects.1
            have afterSemantic : SemanticReady afterEdge := by
              simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint
                values middle childEffects.2.1 childEffects.2.2.2.2
            have afterCosts : CostHeap afterEdge := by
              simpa only [built] using (show CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 from
                childEffects.2.2.1)
            have allKept := childEffects.1.trans afterKept
            have tail := ih rest afterSemantic afterCosts
              (fun row member => edge_grows before afterEdge allKept.growth row (tailResident row member))
            intro output member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨edge, List.mem_cons_self, firstOrigin, unchanged⟩
            · obtain ⟨original, included, kept⟩ := tail output member
              exact ⟨original, List.mem_cons_of_mem _ included, kept⟩
  intro result member
  obtain ⟨original, included, kept⟩ := origin result member
  obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp included
  exact ⟨sourceIndex, original, found, kept⟩

/-- Normalized Required node rows retain an original row and its unselected child. -/
theorem required_node {entries : List (Int × Needed)} {entry : Interned InternedBinderProtocol.NodeKey}
    {originals : List (EdgeValue Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
    {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode (.node entries) (.node entry originals depth free) before result after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before (.node entry originals depth free))
    (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    ∀ edge ∈ nodeEdges result, ∃ sourceIndex original, originals[sourceIndex]? = some original ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original edge ∧ edge.children[index]? = original.children[index]? := by
  have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
  cases actual with
  | identity =>
      intro edge member
      obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp member
      exact ⟨sourceIndex, edge, found, ⟨rfl, rfl, rfl⟩, rfl⟩
  | @ordinary entries originals before rebuilt middle result after entry depth free nonempty actual built =>
      have origins := required_rows actual semantic costs resident index absent
      have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) actual semantic costs
        (fun _ _ _ => trivial) resident
      have fields := EqualityLeafProjectionPhysical.makeNode_edges rebuilt middle
        effects.2.1.ready.semantic.1.normal.facts.coherent effects.2.1.ready.semantic.1.normal.facts.linked effects.2.2.2.2
      intro edge member
      have earlier : edge ∈ nodeEdges (run (makeNode rebuilt) middle).1 := by simpa only [built] using member
      have included : edge ∈ canonicalEdges (surviving rebuilt) := fields ▸ earlier
      exact origins edge (List.mem_filter.mp (canonicalEdges_member _ edge included)).1
  | recursive nonempty recursive => cases recursive

local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq SourceSymbol] [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
open SourceCurrentAllocatedSharedEditGraph

/-- An absent Edit child key retains the complete value at that position. -/
theorem edit_children {width : Nat} {record originals entries offset values before results after}
    (actual : EditChildren (width := width) record originals entries offset values before results after) (index : Nat)
    (absent : SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = none) :
    results[index]? = values[index]? := by
  induction index generalizing offset values results before after with
  | zero =>
      cases actual with
      | nil => rfl
      | unselected => rfl
      | selected index found => simp only [Nat.add_zero] at absent; rw [found] at absent; contradiction
  | succ index ih =>
      cases actual with
      | nil => rfl
      | unselected offset _ rest =>
          exact ih rest (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using absent)
      | selected offset _ _ rest =>
          exact ih rest (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using absent)

end MicroCFTA.SourceCurrentPositionalRowOrigins
