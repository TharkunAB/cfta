import MicroCFTA.SourceCurrentPositiveProjectionSourceRoute

/-!
# Original forest operands of positive projection reads

A completed projection can return a Mu at an empty remaining path. Its actual
row read is part of this theorem. A false primary node trace excludes positive
rows from that accepted Mu. Nonempty projections construct ordinary results.

A nonempty forest path selects its exact original forest position. The route
starts at that value. The empty forest path has no such primary certificate:
its gate returns false without checking any original value.
-/
namespace MicroCFTA.SourceCurrentPositiveForestProjectionOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open EndpointStatefulGateTrace
open SourceCurrentPositiveProjectionSourceRoute (Route)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem ordinary_read {value : Node} (ordinary : Ordinary value) {before rows after}
    (actual : Read value before rows after) : rows = nodeEdges value := by
  cases value with
  | empty | node =>
    cases actual with
    | done fuel completed => exact (MergedSourceExposure.Result.done.inj completed).1.symm
  | reference | union | mu => cases ordinary

private theorem union_ordinary {values before result after}
    (actual : @Union Symbol Guard _ values before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Ordinary result := by
  cases actual with
  | node reads built =>
    have effects := SourceEqualityProjectionCosts.readAll_effects reads semantic costs available
    simpa only [built] using SourceEqualityRequiredCache.node_ordinary _ _
      effects.2.1.ready.semantic.1.normal.facts effects.2.2.2

private theorem project_ordinary {path value before result after}
    (actual : @Project Symbol Guard _ path value before result after) :
    SemanticReady before → CostHeap before → Available before value → path ≠ [] → Ordinary result := by
  induction actual using Project.rec
      (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | root => intro _ _ _ impossible; exact (impossible rfl).elim
  | empty => intro _ _ _ _; trivial
  | ordinary rows combined _ =>
    intro semantic costs available _
    have resident := resident_edges _ semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have effects := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    exact union_ordinary combined effects.2.1 effects.2.2.1 effects.2.2.2
  | recursive _ head _ ih =>
    intro semantic costs available nonempty
    have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact ih effects.2.1 effects.2.2.1 effects.2.2.2 nonempty
  | nil => trivial
  | missing => trivial
  | selected => trivial

/-- A positive actual row read after projection retains the original ordinary source route. -/
theorem project_read (path : EqualityNormalize.Path) (value : Node) (gateBefore gateAfter before after : Heap)
    (result : Node) (gate : NodeTrace source reaches path value gateBefore false gateAfter)
    (initialSemantic : SemanticReady gateBefore)
    (initialNormal : SourceCurrentRequiredUnionNormal.UnionNormal gateBefore)
    (initialAvailable : Available gateBefore value) (retained : Grows gateAfter before)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (actual : Project (path.map Int.ofNat) value before result after)
    (reader : Heap) (readerSemantic : SemanticReady reader) (readerGuards : Guards reader)
    (later : Keeps after reader) (rows : List Row) (readAfter : Heap)
    (read : Read result reader rows readAfter) (row : Row) (selected : row ∈ rows)
    (positive : ¬ Plain row.entry.key.constraint) : Route (path.map Int.ofNat) value row := by
  by_cases ordinary : Ordinary result
  · exact SourceCurrentPositiveProjectionSourceRoute.positive path value gateBefore gateAfter before after result
      gate initialSemantic initialNormal initialAvailable retained semantic costs available guards actual row
      (ordinary_read ordinary read ▸ selected) positive
  have effects := SourceEqualityProjectionCosts.project_effects actual semantic costs available
  have finalAvailable := later.available result effects.2.2.2
  cases path with
  | cons index path =>
    exact (ordinary (project_ordinary actual semantic costs available (by simp))).elim
  | nil =>
    cases actual with
    | root =>
      cases value with
      | empty | node => exact (ordinary trivial).elim
      | reference | union => cases gate
      | mu entry body depth probe =>
        have accepted : source (.mu entry body depth probe) = true := by
          cases gate with
          | closed accepted _ => exact accepted
          | unfold accepted _ _ _ => exact accepted
        have annotated := SourceCurrentGatePlainRegion.annotations gateBefore _
          initialSemantic.ready.semantic.1.normal.facts.coherent initialAvailable accepted
        cases read with
        | done fuel completed =>
          have localRows := SourceCurrentConstrainedCapOpenExposure.nodeEdges Plain 0 fuel _ reader
            readerSemantic.ready.semantic readerSemantic.ready.covered finalAvailable (.plain 0 annotated)
            (SourceCurrentConstrainedCapGuardNative.stored Plain reader readerGuards) rows readAfter completed
          exact (positive ((localRows.2 row selected).1)).elim

/-- A positive read on a nonempty forest path retains its exact original forest index and smaller input continuations. -/
theorem forest_read (index : Nat) (path : EqualityNormalize.Path) (values : List Node)
    (gateBefore gateAfter before after : Heap) (result : Node)
    (gate : PathTrace source reaches values (index :: path) gateBefore false gateAfter)
    (initialSemantic : SemanticReady gateBefore)
    (initialNormal : SourceCurrentRequiredUnionNormal.UnionNormal gateBefore)
    (initialAvailable : Values gateBefore values) (retained : Grows gateAfter before)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (guards : Guards before) (actual : Forest ((index :: path).map Int.ofNat) values before result after)
    (reader : Heap) (readerSemantic : SemanticReady reader) (readerGuards : Guards reader)
    (later : Keeps after reader) (rows : List Row) (readAfter : Heap)
    (read : Read result reader rows readAfter) (row : Row) (selected : row ∈ rows)
    (positive : ¬ Plain row.entry.key.constraint) :
    ∃ value, values[index]? = some value ∧
      Project (path.map Int.ofNat) value before result after ∧ Route (path.map Int.ofNat) value row ∧
      ∀ child ∈ row.children, InternedValueMass.value child < InternedValueMass.value value := by
  cases actual with
  | missing absent =>
    have same := ordinary_read (value := (.empty : Node)) trivial read
    rw [same] at selected
    cases selected
  | selected found body =>
    rename_i value
    have natural : values[index]? = some value := by
      simpa only [select,Int.ofNat_eq_natCast,
        ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using found
    have nodeGate : NodeTrace source reaches path value gateBefore false gateAfter := by
      cases gate with
      | child traced =>
        cases traced with
        | missing absent => rw [absent] at natural; cases natural
        | present chosen node =>
          cases Option.some.inj (chosen.symm.trans natural)
          exact node
    have route := project_read path value gateBefore gateAfter before after result nodeGate initialSemantic
      initialNormal (initialAvailable value (List.mem_of_getElem? natural)) retained semantic costs
      (available value (List.mem_of_getElem? natural)) guards body reader readerSemantic readerGuards later
      rows readAfter read row selected positive
    exact ⟨value,natural,body,route,fun child member => route.mass_lt child member⟩

end MicroCFTA.SourceCurrentPositiveForestProjectionOrigins
