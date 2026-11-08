import MicroCFTA.SourceCurrentPositionalRowOrigins
import MicroCFTA.SourceCurrentLiteralRootParts
import MicroCFTA.MergedFreshOrdinaryExposureOrigins
import MicroCFTA.MergedFreshOrdinaryGraphOrigins
import MicroCFTA.InternedUnionHeadGuard

/-!
# Joint row origins through actual Required reconstruction

One original row accounts for every unselected returned child. The result
includes Top rows. Root union exposure retains literal original rows when
no root union path reaches Mu. The statements concern completed call graphs.
-/
namespace MicroCFTA.SourceCurrentRequiredJointRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredCache (Ordinary)
open SourceCurrentRequiredGuardOrigins (RowOrigin)
open SourceCurrentLiteralRootParts (Row)
open InternedUnionHeadGuard (HeadSafe)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- One indexed original row supplies all absent child positions of a returned row. -/
theorem required_rows {entries : List (Int × Needed)} {originals results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireRows entries originals before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before originals) :
    ∀ result ∈ results, ∃ sourceIndex : Nat, ∃ original, originals[sourceIndex]? = some original ∧
      RowOrigin original result ∧ ∀ index : Nat,
        SourceEqualityNeededMap.lookup (index : Int) entries = none →
          result.children[index]? = original.children[index]? := by
  have origin : ∀ result ∈ results, ∃ original ∈ originals, RowOrigin original result ∧ ∀ index : Nat,
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
        result.children[index]? = original.children[index]? := by
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
            have firstOrigin : RowOrigin edge result :=
              ⟨by simpa only [built] using fields.2.1, by simpa only [built] using fields.1,
                (congrArg List.length equalChildren).trans children.length⟩
            have unchanged : ∀ index : Nat, SourceEqualityNeededMap.lookup (index : Int) entries = none →
                result.children[index]? = edge.children[index]? := by
              intro index absent
              rw [equalChildren]
              exact SourceCurrentPositionalRowOrigins.required_children children index
                (by simpa only [Nat.zero_add] using absent)
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

/-- Ordinary node normalization retains one original row for all absent child positions. -/
theorem required_node {entries : List (Int × Needed)} {entry : Interned InternedBinderProtocol.NodeKey}
    {originals : List (EdgeValue Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
    {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode (.node entries) (.node entry originals depth free) before result after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before (.node entry originals depth free)) :
    ∀ edge ∈ nodeEdges result, ∃ sourceIndex : Nat, ∃ original, originals[sourceIndex]? = some original ∧
      RowOrigin original edge ∧ ∀ index : Nat,
        SourceEqualityNeededMap.lookup (index : Int) entries = none →
          edge.children[index]? = original.children[index]? := by
  have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
  cases actual with
  | identity =>
      intro edge member
      obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp member
      exact ⟨sourceIndex, edge, found, ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  | @ordinary entries originals before rebuilt middle result after entry depth free nonempty actual built =>
      have origins := required_rows actual semantic costs resident
      have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) actual semantic costs
        (fun _ _ _ => trivial) resident
      have fields := EqualityLeafProjectionPhysical.makeNode_edges rebuilt middle
        effects.2.1.ready.semantic.1.normal.facts.coherent effects.2.1.ready.semantic.1.normal.facts.linked effects.2.2.2.2
      intro edge member
      have earlier : edge ∈ nodeEdges (run (makeNode rebuilt) middle).1 := by simpa only [built] using member
      have included : edge ∈ canonicalEdges (surviving rebuilt) := fields ▸ earlier
      exact origins edge (List.mem_filter.mp (canonicalEdges_member _ edge included)).1
  | recursive nonempty recursive => cases recursive

private theorem literal_of_origin {input : Value Symbol Guard} (safe : HeadSafe input)
    (view : State Symbol Guard) (edge : EdgeValue Symbol Guard) :
    MergedFreshOrdinaryGraph.Origin view [input] edge → Row input edge := by
  induction safe with
  | empty =>
      intro origin
      exact False.elim (MergedFreshOrdinaryGraph.origin_empty view edge origin)
  | reference name =>
      intro origin
      have impossible := MergedFreshOrdinaryExposureCoverage.origin_terminal view (.reference name) rfl edge origin
      cases impossible
  | node entry rows depth free =>
      intro origin
      exact .node ((MergedFreshOrdinaryGraph.origin_node view entry rows depth free edge).mp origin)
  | union entry members depth free children ih =>
      intro origin
      obtain ⟨value, member, earlier⟩ :=
        (MergedFreshOrdinaryGraph.origin_union view entry members depth free edge).mp origin
      exact .union member (ih value member earlier)

/-- Actual Head normalization exposes literal original rows when root unions cannot reach Mu. -/
theorem head_literal_rows {input result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head input before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (safe : HeadSafe input) : Ordinary result ∧ ∀ edge ∈ nodeEdges result, Row input edge := by
  cases actual with
  | read fuel edges middle exposed built =>
      have read := SourceEqualityExposureCosts.nodeEdges_verified fuel input before semantic costs available
      have middleSemantic : SemanticReady middle := by
        simpa only [exposed, MergedSourceExposure.Result.state] using read.semantic
      have resident : Edges middle edges := read.rows edges middle exposed
      have facts := middleSemantic.ready.semantic.1.normal.facts
      have fields := EqualityLeafProjectionPhysical.makeNode_edges edges middle facts.coherent facts.linked resident
      have ordinary := SourceEqualityRequiredCache.node_ordinary edges middle facts resident
      have origins := MergedFreshOrdinaryExposureOrigins.nodeEdges_origins fuel input before semantic.ready.semantic
        semantic.ready.covered available edges middle exposed middle (grows_refl _)
      refine ⟨?_, ?_⟩
      · simpa only [built] using ordinary
      · intro edge member
        have earlier : edge ∈ nodeEdges (run (makeNode edges) middle).1 := by simpa only [built] using member
        have included : edge ∈ canonicalEdges (surviving edges) := fields ▸ earlier
        exact literal_of_origin safe middle edge
          (origins edge (List.mem_filter.mp (canonicalEdges_member _ edge included)).1)

private theorem required_ordinary_rows {entries : List (Int × Needed)} {input result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : RequireNode (.node entries) input before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (ordinary : Ordinary input) :
    ∀ edge ∈ nodeEdges result, ∃ original ∈ nodeEdges input, RowOrigin original edge ∧ ∀ index : Nat,
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
        edge.children[index]? = original.children[index]? := by
  cases input with
  | empty =>
      cases actual with
      | identity => intro edge member; cases member
      | empty nonempty => intro edge member; cases member
      | recursive nonempty recursive => cases recursive
  | node entry rows depth free =>
      intro edge member
      obtain ⟨sourceIndex, original, found, origin, unchanged⟩ := required_node actual semantic costs available edge member
      exact ⟨original, List.mem_of_getElem? found, origin, unchanged⟩
  | reference | union | mu => cases ordinary

/-- One literal source row supplies the full guard and every unselected child after Required. -/
theorem required_literal_rows {entries : List (Int × Needed)} {input result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : RequireNode (.node entries) input before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (safe : HeadSafe input) :
    ∀ edge ∈ nodeEdges result, ∃ original, Row input original ∧ RowOrigin original edge ∧ ∀ index : Nat,
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
        edge.children[index]? = original.children[index]? := by
  cases actual with
  | identity =>
      intro edge member
      have literal : Row input edge := by
        cases input with
        | node entry rows depth free => exact .node member
        | empty | reference | union | mu => cases member
      exact ⟨edge, literal, ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  | empty nonempty => intro edge member; cases member
  | @ordinary entries originals before rebuilt middle result after entry depth free nonempty rows built =>
      intro edge member
      obtain ⟨sourceIndex, original, found, origin, unchanged⟩ :=
        required_node (.ordinary nonempty rows built) semantic costs available edge member
      exact ⟨original, .node (List.mem_of_getElem? found), origin, unchanged⟩
  | @recursive entries input before exposed middle result after nonempty recursive head body =>
      have exposedRows := head_literal_rows head semantic costs available safe
      have effects := SourceCurrentRequiredHeapEffects.head (fun _ => True) head semantic costs
        (fun _ _ _ => trivial) available
      have origins := required_ordinary_rows body effects.2.1 effects.2.2.1 effects.2.2.2.2 exposedRows.1
      intro edge member
      obtain ⟨original, included, origin, unchanged⟩ := origins edge member
      exact ⟨original, exposedRows.2 original included, origin, unchanged⟩

end MicroCFTA.SourceCurrentRequiredJointRowOrigins
