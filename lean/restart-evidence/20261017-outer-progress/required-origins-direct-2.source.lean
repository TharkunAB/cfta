import MicroCFTA.SourceCurrentGatePlainRegion
import MicroCFTA.SourceCurrentConstrainedCapOpenExposure
import MicroCFTA.SourceCurrentConstrainedCapSelectedRequired
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Guard origins through actual Required reconstruction

An ordinary root keeps a full guard from an original root row. Child
reconstruction does not require an annotation on unrelated children.
The actual plain gate supplies local annotations for recursive exposure.
Causal guard observations retain them through actual stored unfolding,
Head, and Required returns. These are completed-read results. They do not
establish an origin-stratified decreasing outer recursion measure.
-/
namespace MicroCFTA.SourceCurrentRequiredGuardOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph SourceEqualityAnnotationLanguage
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual returned row retains its original full guard, symbol, and ordered arity. -/
def RowOrigin (original result : EdgeValue Symbol Guard) : Prop :=
  result.entry.key.constraint = original.entry.key.constraint ∧
    result.entry.key.symbol = original.entry.key.symbol ∧ result.children.length = original.children.length

/-- Every returned root row has an actual original row, without any child-annotation premise. -/
theorem rows {entries : List (Int × Needed)} {originals results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireRows entries originals before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before originals) :
    ∀ result ∈ results, ∃ original ∈ originals, RowOrigin original result := by
  induction originals generalizing results before after with
  | nil => cases actual; intro result member; cases member
  | cons edge edges ih =>
      have tailResident : Edges before edges := fun row member => resident row (List.mem_cons_of_mem _ member)
      cases actual with
      | rejected rejected rest =>
          intro result member
          obtain ⟨original, included, origin⟩ := ih rest semantic costs tailResident result member
          exact ⟨original, List.mem_cons_of_mem _ included, origin⟩
      | @kept _ _ values middle result afterEdge _ _ _ _ fits children built rest =>
          have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
            edge.entry.key edge (resident edge List.mem_cons_self)
          have childEffects := SourceCurrentRequiredHeapEffects.children (fun _ => True) children semantic costs
            (fun _ _ _ => trivial) available
          have fields := MergedPhysicalGroupEdges.makeEdge_fields middle childEffects.2.1.ready.semantic.1.normal.facts
            edge.entry.key.symbol edge.entry.key.constraint values childEffects.2.2.2.2
          have firstOrigin : RowOrigin edge result := by
            dsimp only [RowOrigin]
            have equalChildren : result.children = values := by simpa only [built] using fields.2.2
            exact ⟨by simpa only [built] using fields.2.1,
              by simpa only [built] using fields.1, (congrArg List.length equalChildren).trans children.length⟩
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
          · exact ⟨edge, List.mem_cons_self, firstOrigin⟩
          · obtain ⟨original, included, origin⟩ := tail output member
            exact ⟨original, List.mem_cons_of_mem _ included, origin⟩

/-- Ordinary Required roots copy their returned row guards from the literal original root. -/
theorem ordinary {needed : Needed} {entry : Interned InternedBinderProtocol.NodeKey}
    {originals : List (EdgeValue Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
    {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed (.node entry originals depth free) before result after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before (.node entry originals depth free)) :
    ∀ edge ∈ nodeEdges result, ∃ original ∈ originals, RowOrigin original edge := by
  have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
  cases actual with
  | identity => exact fun edge member => ⟨edge, member, rfl, rfl, rfl⟩
  | @ordinary entries originals before rebuilt middle result after entry depth free nonempty actual built =>
      have origins := rows actual semantic costs resident
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
local notation "Plain" => (fun guard : SourceGuard => SourceMemoGate.plain guard = true)
variable [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap

private theorem empty_rows {value : Value SourceSymbol SourceGuard} (annotated : Annotated Plain value) :
    ∀ edge ∈ nodeEdges value, SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []) :=
  fun edge member => SourceCurrentHereditaryUnconstrained.plain_physical _
    (SourceCurrentHereditaryUnconstrained.node_edge annotated edge member).1

private theorem unfold_heap (value : Value SourceSymbol SourceGuard) (before : State SourceSymbol SourceGuard)
    (semantic : SemanticReady before) (available : Available before value) (guards : GuardHeap Plain before) :
    GuardHeap Plain (InternedFreshOrdinaryStoredSubstitution.unfold value before).state := by
  cases value with
  | empty | reference | node | union => exact guards
  | mu entry body depth ordinary =>
      apply SourceCurrentConstrainedCapGuardNative.execute_heap Plain body _ before semantic.ready.semantic
        (available.children body (by simp [InternedProbeProvenance.children])) _ guards
      intro name replacement found
      dsimp only at found
      split at found
      · cases found; exact available
      · cases found

/-- Literal unfolding of a gate-accepted region adds no nonempty own equality field. -/
theorem accepted_unfold {value result : Value SourceSymbol SourceGuard} {before after : State SourceSymbol SourceGuard}
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after)
    (semantic : SemanticReady before) (available : Available before value) (guards : GuardHeap Plain before)
    (accepted : SourceMemoGate.unconstrained value = true) :
    GuardHeap Plain after ∧ Annotated Plain result ∧
      ∀ edge ∈ nodeEdges result, SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []) := by
  have annotated := SourceCurrentGatePlainRegion.annotations before value semantic.ready.semantic.1.normal.facts.coherent available accepted
  have produced := SourceCurrentHereditaryConstruction.unfold Plain value before semantic.ready.semantic.1.normal.facts available annotated
    (SourceCurrentConstrainedCapGuardNative.stored Plain before guards)
  have localResult := produced.result result after actual
  refine ⟨?_, localResult, empty_rows localResult⟩
  simpa only [actual, InternedNestedConstruction.Outcome.state] using unfold_heap value before semantic available guards

/-- Actual Head of a gate-accepted region retains zero-origin rows at its exact returned heap. -/
theorem accepted_head {value result : Value SourceSymbol SourceGuard} {before after : State SourceSymbol SourceGuard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : GuardHeap Plain before) (accepted : SourceMemoGate.unconstrained value = true) :
    GuardHeap Plain after ∧ Annotated Plain result ∧
      ∀ edge ∈ nodeEdges result, SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []) := by
  have annotated := SourceCurrentGatePlainRegion.annotations before value semantic.ready.semantic.1.normal.facts.coherent available accepted
  have returned := SourceCurrentConstrainedCapOpenExposure.head Plain 0 actual semantic costs available
    (.plain 0 annotated) (SourceCurrentConstrainedCapGuardNative.stored Plain before guards)
  have localResult := returned.2.annotated rfl
  exact ⟨SourceCurrentConstrainedCapProjectionGuard.head Plain actual semantic costs available guards,
    localResult, empty_rows localResult⟩

/-- Required preserves zero-origin guards from an actual accepted input, with no global plain heap. -/
theorem accepted_node {needed : Needed} {value result : Value SourceSymbol SourceGuard} {before after : State SourceSymbol SourceGuard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (guards : GuardHeap Plain before) (accepted : SourceMemoGate.unconstrained value = true) :
    GuardHeap Plain after ∧ Annotated Plain result ∧
      ∀ edge ∈ nodeEdges result, SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []) := by
  have annotated := SourceCurrentGatePlainRegion.annotations before value semantic.ready.semantic.1.normal.facts.coherent available accepted
  have returned := SourceCurrentConstrainedCapSelectedRequired.node Plain 0 actual semantic costs available guards (.plain 0 annotated)
  have localResult := returned.2.annotated rfl
  exact ⟨returned.1, localResult, empty_rows localResult⟩

end MicroCFTA.SourceCurrentRequiredGuardOrigins
