import MicroCFTA.SourceCurrentPrimaryEndpointCap
import MicroCFTA.SourceCurrentRequiredProjectionOrigins
import MicroCFTA.SourceCurrentRecursivePlainRead
import MicroCFTA.SourceCurrentConstrainedCapOpenExposure

/-! # Local projection caps from the original false primary gate -/
namespace MicroCFTA.SourceCurrentOriginalGateProjectionCap
open InternedRecordCoherence
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceEqualityAnnotationLanguage EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (Origin RowMap ChildMap)
open SourceCurrentConstrainedCap (Cap Edge)
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
private def Finite (value : Node) : Prop := ∃ depth, Cap Plain depth value

private theorem uniform (values : List Node) (all : ∀ value ∈ values, Finite value) :
    ∃ depth, ∀ value ∈ values, Cap Plain depth value := by
  induction values with
  | nil => exact ⟨0,by intro value member; cases member⟩
  | cons value values ih =>
    obtain ⟨first,bounded⟩ := all value List.mem_cons_self
    obtain ⟨rest,others⟩ := ih (fun child member => all child (List.mem_cons_of_mem _ member))
    refine ⟨max first rest,?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | later
    · exact bounded.mono (Nat.le_max_left _ _)
    · exact (others child later).mono (Nat.le_max_right _ _)

private theorem child_finite {value : Node} (bounded : Finite value) (row : Row)
    (member : row ∈ nodeEdges value) (child : Node) (inside : child ∈ row.children) : Finite child := by
  obtain ⟨depth,bounded⟩ := bounded
  have localRow := SourceCurrentConstrainedCap.node_edge bounded row member
  cases depth with
  | zero => exact ⟨0,.plain 0 (localRow.2 child inside)⟩
  | succ depth => exact ⟨depth,localRow child inside⟩

private theorem ordinary_finite (value : Node) (ordinary : Ordinary value)
    (children : ∀ row ∈ nodeEdges value, ∀ child ∈ row.children, Finite child) : Finite value := by
  cases value with
  | empty => exact ⟨0,.plain 0 .empty⟩
  | reference | union | mu => cases ordinary
  | node entry rows depth free =>
    obtain ⟨bound,bounded⟩ := uniform (rows.flatMap EdgeValue.children) (by
      intro child member
      obtain ⟨row,selected,inside⟩ := List.mem_flatMap.mp member
      exact children row selected child inside)
    exact ⟨bound+1,.node bound entry rows depth free bounded⟩

private theorem origin_finite {original prepared : Node} (origin : Origin original prepared) :
    Finite original → Finite prepared := by
  apply Origin.rec
    (motive_1 := fun original prepared _ => Finite original → Finite prepared)
    (motive_2 := fun originals outputs _ =>
      (∀ row ∈ originals, ∀ child ∈ row.children, Finite child) →
      ∀ row ∈ outputs, ∀ child ∈ row.children, Finite child)
    (motive_3 := fun originals outputs _ =>
      (∀ child ∈ originals, Finite child) → ∀ child ∈ outputs, Finite child)
    (t := origin)
  · intro value bounded; exact bounded
  · intro original prepared annotated _; exact ⟨0,.plain 0 annotated⟩
  · intro entry originals level free result ordinary mapped ih bounded
    exact ordinary_finite result ordinary (ih (fun row member child inside => child_finite bounded row member child inside))
  · intro originals _ row member; cases member
  · intro originals outputs sourceIndex original output found fields children rest childIH restIH rows row member
    rcases List.mem_cons.mp member with rfl | later
    · exact childIH (rows original (List.mem_of_getElem? found))
    · exact restIH rows row later
  · intro children child member; cases member
  · intro original output originals outputs first rest firstIH restIH children child member
    rcases List.mem_cons.mp member with rfl | later
    · exact firstIH (children original List.mem_cons_self)
    · exact restIH (fun child member => children child (List.mem_cons_of_mem _ member)) child later

private inductive Corridor : List Int → Node → Prop where
  | full (path value) (bounded : Finite value) : Corridor path value
  | node (entry) (rows : List Row) (depth free index path)
      (children : ∀ row ∈ rows, ∀ child, select row.children index = some child → Corridor path child) :
      Corridor (index::path) (.node entry rows depth free)

private theorem corridor_origin {path original prepared} (safe : Corridor path original)
    (origin : Origin original prepared) : Corridor path prepared := by
  induction path generalizing original prepared with
  | nil => cases safe with | full _ _ bounded => exact .full _ _ (origin_finite origin bounded)
  | cons index path ih =>
    cases origin with
    | identity value => exact safe
    | plain original prepared annotated => exact .full _ _ ⟨0,.plain 0 annotated⟩
    | ordinary entry originals level free prepared ordinary mapped =>
      cases safe with
      | full _ _ bounded => exact .full _ _ (origin_finite (.ordinary entry originals level free prepared ordinary mapped) bounded)
      | node _ _ _ _ _ _ children =>
        cases prepared with
        | empty => exact .full _ _ ⟨0,.plain 0 .empty⟩
        | reference | union | mu => cases ordinary
        | node entry rows depth free =>
          apply Corridor.node
          intro row member child selected
          obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
          obtain ⟨sourceIndex,sourceRow,original,fields,related⟩ := mapped.indexed position row found
          obtain ⟨sourceChild,sourceFound,childOrigin⟩ := SourceEqualityProjectionLanguage.all₂_signed related index child selected
          exact ih (children sourceRow (List.mem_of_getElem? original) sourceChild sourceFound) childOrigin

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]
private theorem false_edges (index : Nat) (path : EqualityNormalize.Path) (rows : List Row)
    (before after : Heap) (trace : EdgesTrace source reaches index path rows before false after)
    (semantic : SemanticReady before) (available : Values before (rows.flatMap EdgeValue.children))
    (target : Heap) (retained : Grows after target) :
    ∀ row ∈ rows, ChildTrace source reaches row.children index path target false target := by
  induction rows generalizing before with
  | nil => intro row member; cases member
  | cons first rest ih =>
    cases trace with
    | next head tail =>
      have initial := SourceCurrentPrimaryReplay.child_replay source reaches _ _ _ _ _ _ head semantic
        (fun value member => available value (by simp [member]))
      have nextAvailable : Values _ (rest.flatMap EdgeValue.children) :=
        fun value member => initial.2.1.available value (available value (by simp [member]))
      have later := SourceCurrentPrimaryReplay.edges_replay source reaches _ _ _ _ _ _ tail initial.1 nextAvailable
      intro row member
      rcases List.mem_cons.mp member with rfl | included
      · exact initial.2.2 target (grows_trans later.2.1.growth retained)
      · exact ih _ tail initial.1 nextAvailable row included

private theorem false_selected {values : List Node} {index : Nat} {path : EqualityNormalize.Path}
    {value : Node} {before after : Heap} (trace : ChildTrace source reaches values index path before false after)
    (found : values[index]? = some value) : NodeTrace source reaches path value before false after := by
  cases trace with
  | missing absent => rw [absent] at found; cases found
  | present selected node => cases Option.some.inj (selected.symm.trans found); exact node

private theorem gate_corridor (path : List Nat) (value : Node) (anchor before after : Heap)
    (semantic : SemanticReady anchor) (available : Available anchor value)
    (current : SemanticReady before) (resident : Available before value)
    (gate : NodeTrace source reaches path value before false after) : Corridor (path.map Int.ofNat) value := by
  induction path generalizing value before after with
  | nil => exact .full _ _ ⟨_,SourceCurrentPrimaryEndpointCap.endpoint_cap before
      current.ready.semantic.1.normal.facts.coherent value resident gate⟩
  | cons index path ih =>
    cases value with
    | empty => exact .full _ _ ⟨0,.plain 0 .empty⟩
    | reference | union => cases gate
    | mu entry body depth ordinary =>
      have accepted : source (.mu entry body depth ordinary) = true := by
        cases gate with
        | closed accepted _ => exact accepted
        | unfold accepted _ _ _ => exact accepted
      exact .full _ _ ⟨0,.plain 0 (SourceCurrentGatePlainRegion.annotations anchor _
        semantic.ready.semantic.1.normal.facts.coherent available accepted)⟩
    | node entry rows depth free =>
      cases gate with
      | finite fast =>
        exact .full _ _ ⟨_,SourceCurrentPrimaryEndpointCap.reaches_cap anchor
          semantic.ready.semantic.1.normal.facts.coherent _ available
          (SourceEndpointReachability.zero_clear source _
            (by simpa only [Value.depth,beq_iff_eq] using (Bool.and_eq_true_iff.mp fast).1))⟩
      | branches slow scanned =>
        have effects := SourceCurrentPrimaryReplay.edges_replay source reaches index path rows before false after
          scanned current (fun child member => resident.children child member)
        apply Corridor.node entry rows depth free (Int.ofNat index) (path.map Int.ofNat)
        intro row member child found
        have natural : row.children[index]? = some child := by
          simpa only [select,Int.ofNat_eq_natCast,
            ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using found
        have traced := false_selected (false_edges index path rows before after scanned current
          (fun child member => resident.children child member) after (grows_refl _) row member) natural
        have inside := List.mem_flatMap.mpr ⟨row,member,select_member found⟩
        exact ih child after after (available.children child inside) effects.1
          (effects.2.1.available child (resident.children child inside)) traced

private theorem readAll_caps (depth : Nat) {values : List Node} {before after : Heap} {rows : List Row}
    (actual : ReadAll values before rows after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (guards : Guards before) (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∀ row ∈ rows, Edge Plain depth row := by
  induction actual with
  | nil => intro row member; cases member
  | @cons value before rows middle values more after first rest ih =>
    have firstCap : ∀ row ∈ rows, Edge Plain depth row := by
      cases first with
      | done fuel completed => exact (SourceCurrentConstrainedCapOpenExposure.nodeEdges Plain depth fuel value before
          semantic.ready.semantic semantic.ready.covered (available _ List.mem_cons_self)
          (bounded _ List.mem_cons_self) (SourceCurrentConstrainedCapGuardNative.stored Plain before guards) rows middle completed).2
    have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
    have tail := ih effects.2.1 effects.2.2.1
      (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member)))
      (SourceCurrentConstrainedCapProjectionGuard.read Plain first semantic costs (available _ List.mem_cons_self) guards)
      (fun child member => bounded child (List.mem_cons_of_mem _ member))
    intro row member
    rcases List.mem_append.mp member with own | later
    · exact firstCap row own
    · exact tail row later

private theorem union_finite {values : List Node} {before after : Heap} {result : Node}
    (actual : Union values before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (guards : Guards before) (bounded : ∀ value ∈ values, Finite value) : Finite result := by
  obtain ⟨depth,caps⟩ := uniform values bounded
  cases actual with
  | node rows built =>
    have boundedRows := readAll_caps depth rows semantic costs available guards caps
    have effects := SourceEqualityProjectionCosts.readAll_effects rows semantic costs available
    have facts := effects.2.1.ready.semantic.1.normal.facts
    refine ⟨depth, ?_⟩
    simpa only [built] using (SourceCurrentConstrainedCap.makeNode Plain depth _ _
      facts.coherent facts.linked effects.2.2.2 boundedRows)

private theorem rows_guards {path index} {rows : List Row} {before values after}
    (actual : ProjectRows path index rows before values after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before rows) (guards : Guards before) : Guards after := by
  induction rows generalizing before values after with
  | nil => cases actual; exact guards
  | cons row rows ih =>
    cases actual with
    | missing absent rest => exact ih rest semantic costs (fun row member => resident row (List.mem_cons_of_mem _ member)) guards
    | selected chosen first rest =>
      have available := semantic.ready.semantic.1.normal.facts.cached.edges row.entry.key row (resident row List.mem_cons_self) _ (select_member chosen)
      have phase := SourceEqualityProjectionCosts.project_effects first semantic costs available
      exact ih rest phase.2.1 phase.2.2.1 (fun row member => edge_grows before _ phase.1.growth row (resident row (List.mem_cons_of_mem _ member)))
        (SourceCurrentConstrainedCapProjectionGuard.node Plain first semantic costs available guards)


private def NodePost (path : List Int) (value : Node) (before : Heap) (result : Node) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Guards before → Corridor path value → Finite result
private def RowsPost (path : List Int) (index : Int) (rows : List Row) (before : Heap) (results : List Node) : Prop :=
  SemanticReady before → CostHeap before → Edges before rows → Guards before →
    (∀ row ∈ rows, ∀ child, select row.children index = some child → Corridor path child) →
    ∀ value ∈ results, Finite value

private theorem project_corridor {path value before result after} (actual : Project path value before result after) :
    NodePost path value before result := by
  have rootCase : ∀ {value : Node} {state}, NodePost [] value state value := by
    intro value state _ _ _ _ safe
    cases safe with | full _ _ bounded => exact bounded
  have emptyCase : ∀ {index path state}, NodePost (index::path) (.empty : Node) state .empty := by
    intro index path state _ _ _ _ _; exact ⟨0,.plain 0 .empty⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows path index edges before values middle → Union values middle result after →
      RowsPost path index edges before values → NodePost (index::path) (.node entry edges depth free) before result := by
    intro path index edges before values middle result after entry depth free rows combined ih semantic costs available guards safe
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have selected : ∀ row ∈ edges, ∀ child, select row.children index = some child → Corridor path child := by
      cases safe with
      | node _ _ _ _ _ _ children => exact children
      | full _ _ bounded => exact fun row member child found => .full _ _ (child_finite bounded row member child (select_member found))
    have children := ih semantic costs resident guards selected
    have effects := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    exact union_finite combined effects.2.1 effects.2.2.1 effects.2.2.2
      (rows_guards rows semantic costs resident guards) children
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (index::path) exposed middle result after → NodePost (index::path) exposed middle result →
      NodePost (index::path) original before result := by
    intro original before exposed middle path index result after recursive head _ ih semantic costs available guards safe
    have finite : Finite original := by
      cases safe with
      | full _ _ bounded => exact bounded
      | node => cases recursive
    obtain ⟨depth,bounded⟩ := finite
    have exposedCap := SourceCurrentConstrainedCapOpenExposure.head Plain depth head semantic costs available bounded
      (SourceCurrentConstrainedCapGuardNative.stored Plain before guards)
    have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact ih effects.2.1 effects.2.2.1 effects.2.2.2
      (SourceCurrentConstrainedCapProjectionGuard.head Plain head semantic costs available guards) (.full _ _ ⟨depth,exposedCap.2⟩)
  have nilCase : ∀ {path index state}, RowsPost path index ([] : List Row) state [] := by
    intro path index state _ _ _ _ _ value member; cases member
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows path index edges before results after → RowsPost path index edges before results →
      RowsPost path index (edge::edges) before results := by
    intro edge path index edges before results after _ _ ih semantic costs resident guards safe
    exact ih semantic costs (fun row member => resident row (List.mem_cons_of_mem _ member)) guards
      (fun row member child found => safe row (List.mem_cons_of_mem _ member) child found)
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project path child before result middle →
      ProjectRows path index edges middle results after → NodePost path child before result →
      RowsPost path index edges middle results → RowsPost path index (edge::edges) before (result::results) := by
    intro edge index child path before result middle edges results after found first rest firstIH restIH semantic costs resident guards safe
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    have bounded := firstIH semantic costs available guards (safe edge List.mem_cons_self child found)
    have effects := SourceEqualityProjectionCosts.project_effects first semantic costs available
    have tail := restIH effects.2.1 effects.2.2.1
      (fun row member => edge_grows before middle effects.1.growth row (resident row (List.mem_cons_of_mem _ member)))
      (SourceCurrentConstrainedCapProjectionGuard.node Plain first semantic costs available guards)
      (fun row member child found => safe row (List.mem_cons_of_mem _ member) child found)
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact bounded
    · exact tail value later
  exact Project.rec (motive_1 := fun path value before result _ _ => NodePost path value before result)
    (motive_2 := fun path index rows before results _ _ => RowsPost path index rows before results)
    rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- The original false gate and actual Required origin supply the projected value's finite cap. -/
theorem project (path : List Nat) (original prepared : Node) (gateBefore gateAfter before after : Heap) (result : Node)
    (origin : Origin original prepared) (gate : NodeTrace source reaches path original gateBefore false gateAfter)
    (initialSemantic : SemanticReady gateBefore) (initialAvailable : Available gateBefore original)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before prepared)
    (guards : Guards before) (actual : Project (path.map Int.ofNat) prepared before result after) :
    ∃ depth, Cap Plain depth result :=
  project_corridor actual semantic costs available guards
    (corridor_origin (gate_corridor path original gateBefore gateBefore gateAfter initialSemantic initialAvailable
      initialSemantic initialAvailable gate) origin)
end Actual
end MicroCFTA.SourceCurrentOriginalGateProjectionCap

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentOriginalGateProjectionCap.project
#print MicroCFTA.SourceCurrentOriginalGateProjectionCap.project
#print axioms MicroCFTA.SourceCurrentOriginalGateProjectionCap.project
