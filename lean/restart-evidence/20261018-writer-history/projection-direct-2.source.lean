import MicroCFTA.SourceCurrentPrimaryReplay
import MicroCFTA.SourceCurrentRequiredFiniteExposure
import MicroCFTA.SourceCurrentProjectionIndexedOrigins
import MicroCFTA.SourceCurrentConstrainedCapOpenExposure
import MicroCFTA.SourceCurrentRequiredGuardOrigins
import MicroCFTA.InternedValueMass

/-!
# Ordinary source routes for positive projected rows

A false primary path retains recursive gate acceptance. Accepted recursive
regions have plain guards through actual Head and projection calls. A positive
row therefore follows indexed ordinary children of the projection operand.
The same complete row occurs at the source endpoint.

The historical union-normalization premise handles the finite gate shortcut.
Semantic readiness alone does not supply that separate invariant. The operand
can be a result of earlier edits. This theorem does not identify it with an
initial outer input or prove progress through all selected edits.
-/
namespace MicroCFTA.SourceCurrentPositiveProjectionSourceRoute
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityAnnotationLanguage
open EndpointStatefulGateTrace
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

/-- An indexed ordinary route retains the complete source row and each selected child. -/
inductive Route : List Int → Node → Row → Prop where
  /-- The endpoint selects a complete row in an original ordinary node. -/
  | root (entry) (rows : List Row) (depth free) (position : Nat) (row : Row)
      (found : rows[position]? = some row) : Route [] (.node entry rows depth free) row
  /-- One path component selects an indexed row and its literal child. -/
  | child (entry) (rows : List Row) (depth free) (position : Nat) (original : Row)
      (found : rows[position]? = some original) (index : Int) (value : Node)
      (selected : select original.children index = some value)
      (rest : Route path value row) : Route (index :: path) (.node entry rows depth free) row

/-- Every continuation in the retained endpoint row has smaller mass than the route operand. -/
theorem Route.mass_lt {path value row} (route : Route path value row)
    (child : Node) (member : child ∈ row.children) :
    InternedValueMass.value child < InternedValueMass.value value := by
  induction route with
  | root entry rows depth free position row found =>
    exact InternedValueMass.node_child_lt entry rows depth free row (List.mem_of_getElem? found) child member
  | child entry rows depth free position original found index value selected rest ih =>
    exact Nat.lt_trans (ih member) (InternedValueMass.node_child_lt entry rows depth free original
      (List.mem_of_getElem? found) value (select_member selected))

private inductive Safe (accept : Row → Prop) : List Int → Node → Prop where
  | empty (path) : Safe accept path .empty
  | plain (path value) (annotated : Annotated Plain value) : Safe accept path value
  | root (entry) (rows : List Row) (depth free) (accepted : ∀ row ∈ rows, accept row) :
      Safe accept [] (.node entry rows depth free)
  | node (entry) (rows : List Row) (depth free) (index path)
      (children : ∀ row ∈ rows, ∀ child, select row.children index = some child → Safe accept path child) :
      Safe accept (index :: path) (.node entry rows depth free)

private theorem safe_map {accept other : Row → Prop} {path value}
    (safe : Safe accept path value) (transfer : ∀ row, accept row → other row) : Safe other path value := by
  induction safe with
  | empty path => exact .empty path
  | plain path value annotated => exact .plain path value annotated
  | root entry rows depth free accepted => exact .root entry rows depth free (fun row member => transfer row (accepted row member))
  | node entry rows depth free index path children ih =>
    exact .node entry rows depth free index path (fun row member child found => ih row member child found)

private theorem child_closed {values : List Node} (closed : childFree values = [])
    (value : Node) (member : value ∈ values) : value.free = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name included
  have found := (childFree_member values name).mpr ⟨value,member,included⟩
  rw [closed] at found
  cases found

private theorem safe_finite (path : List Int) (state : Heap) (semantic : SemanticReady state)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal state) (value : Node)
    (available : Available state value) (zero : value.depth = 0) (closed : value.free = []) :
    Safe (Route path value) path value := by
  induction path generalizing value with
  | nil =>
    have ordinary := SourceCurrentRequiredFiniteExposure.ordinary_of_zero_closed state semantic normal value available zero closed
    cases value with
    | empty => exact .empty []
    | reference | union | mu => cases ordinary
    | node entry rows depth free =>
      exact .root entry rows depth free (fun row member => by
        obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
        exact .root entry rows depth free position row found)
  | cons index path ih =>
    have ordinary := SourceCurrentRequiredFiniteExposure.ordinary_of_zero_closed state semantic normal value available zero closed
    cases value with
    | empty => exact .empty _
    | reference | union | mu => cases ordinary
    | node entry rows depth free =>
      apply Safe.node entry rows depth free index path
      intro row member child found
      have inside := List.mem_flatMap.mpr ⟨row,member,select_member found⟩
      have bounded := InternedUnionSeparation.child_depth state semantic.ready.semantic.1.normal.facts.coherent
        (.node entry rows depth free) child available inside
      have names := InternedNormalizationFree.node_free state semantic.ready.semantic.1.normal.facts.coherent
        entry rows depth free available.resident
      have childSafe := ih child (available.children child inside) (by rw [zero] at bounded; omega)
        (child_closed (names.symm.trans closed) child inside)
      apply safe_map childSafe
      intro result route
      obtain ⟨position,present⟩ := List.mem_iff_getElem?.mp member
      exact .child entry rows depth free position row present index child found route

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
    {value : Node} {before after : Heap}
    (trace : ChildTrace source reaches values index path before false after)
    (found : values[index]? = some value) : NodeTrace source reaches path value before false after := by
  cases trace with
  | missing absent => rw [absent] at found; cases found
  | present selected node =>
    cases Option.some.inj (selected.symm.trans found)
    exact node

private theorem safe_gate (path : EqualityNormalize.Path) (value : Node)
    (anchor before after : Heap) (semantic : SemanticReady anchor)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal anchor) (available : Available anchor value)
    (current : SemanticReady before) (resident : Available before value)
    (gate : NodeTrace source reaches path value before false after) :
    Safe (Route (path.map Int.ofNat) value) (path.map Int.ofNat) value := by
  induction path generalizing value before after with
  | nil =>
    cases value with
    | empty => exact .empty []
    | reference | union => cases gate
    | node entry rows depth free =>
      exact .root entry rows depth free (fun row member => by
        obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
        exact .root entry rows depth free position row found)
    | mu entry body depth ordinary =>
      have accepted : source (.mu entry body depth ordinary) = true := by
        cases gate with
        | closed accepted _ => exact accepted
        | unfold accepted _ _ _ => exact accepted
      exact .plain _ _ (SourceCurrentGatePlainRegion.annotations anchor _
        semantic.ready.semantic.1.normal.facts.coherent available accepted)
  | cons index path ih =>
    cases value with
    | empty => exact .empty _
    | reference | union => cases gate
    | mu entry body depth ordinary =>
      have accepted : source (.mu entry body depth ordinary) = true := by
        cases gate with
        | closed accepted _ => exact accepted
        | unfold accepted _ _ _ => exact accepted
      exact .plain _ _ (SourceCurrentGatePlainRegion.annotations anchor _
        semantic.ready.semantic.1.normal.facts.coherent available accepted)
    | node entry rows depth free =>
      cases gate with
      | finite fast =>
        exact safe_finite _ anchor semantic normal _ available
          (by simpa only [Value.depth,beq_iff_eq] using (Bool.and_eq_true_iff.mp fast).1)
          (List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp fast).2)
      | branches slow scanned =>
        have effects := SourceCurrentPrimaryReplay.edges_replay source reaches index path rows before false after
          scanned current (fun child member => resident.children child member)
        apply Safe.node entry rows depth free (Int.ofNat index) (path.map Int.ofNat)
        intro row member child found
        have natural : row.children[index]? = some child := by
          simpa only [select,Int.ofNat_eq_natCast,
            ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using found
        have traced := false_selected
          (false_edges index path rows before after scanned current
            (fun child member => resident.children child member) after (grows_refl _) row member) natural
        have inside := List.mem_flatMap.mpr ⟨row,member,select_member found⟩
        have next := ih child after after (available.children child inside) effects.1
          (effects.2.1.available child (resident.children child inside)) traced
        apply safe_map next
        intro result route
        obtain ⟨position,present⟩ := List.mem_iff_getElem?.mp member
        exact .child entry rows depth free position row present (Int.ofNat index) child found route

private def Accepted (accept : Row → Prop) (value : Node) : Prop :=
  ∀ before rows after, Read value before rows after → SemanticReady before → CostHeap before →
    Available before value → Guards before → ∀ row ∈ rows, ¬ Plain row.entry.key.constraint → accept row

private theorem plain_accepted {accept : Row → Prop} {value : Node} (annotated : Annotated Plain value) :
    Accepted accept value := by
  intro before rows after actual semantic _ available guards row member positive
  cases actual with
  | done fuel completed =>
    have bounded := SourceCurrentConstrainedCapOpenExposure.nodeEdges Plain 0 fuel value before
      semantic.ready.semantic semantic.ready.covered available (.plain 0 annotated)
      (SourceCurrentConstrainedCapGuardNative.stored Plain before guards) rows after completed
    exact False.elim (positive ((bounded.2 row member).1))

private theorem ordinary_read {value : Node} (ordinary : Ordinary value) {before rows after}
    (actual : Read value before rows after) : rows = nodeEdges value := by
  cases value with
  | empty | node =>
    cases actual with
    | done fuel completed => exact (MergedSourceExposure.Result.done.inj completed).1.symm
  | reference | union | mu => cases ordinary

private theorem ordinary_accepted {accept : Row → Prop} {value : Node} (ordinary : Ordinary value)
    (accepted : ∀ row ∈ nodeEdges value, ¬ Plain row.entry.key.constraint → accept row) : Accepted accept value := by
  intro before rows after actual _ _ _ _ row member positive
  exact accepted row (ordinary_read ordinary actual ▸ member) positive

private theorem union_accepted {accept : Row → Prop} {values before result after}
    (actual : Union values before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (guards : Guards before)
    (accepted : ∀ value ∈ values, Accepted accept value) : Accepted accept result := by
  have readsAccepted : ∀ {values before rows after}, ReadAll values before rows after →
      SemanticReady before → CostHeap before → Values before values → Guards before →
      (∀ value ∈ values, Accepted accept value) → ∀ row ∈ rows, ¬ Plain row.entry.key.constraint → accept row := by
    intro values before rows after actual
    induction actual with
    | nil => intro _ _ _ _ _ row member; cases member
    | @cons value before rows middle values more after first rest ih =>
      intro semantic costs available guards accepted row member positive
      have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      rcases List.mem_append.mp member with here | later
      · exact accepted value List.mem_cons_self _ _ _ first semantic costs (available _ List.mem_cons_self) guards row here positive
      · exact ih effects.2.1 effects.2.2.1
          (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
          (SourceCurrentConstrainedCapProjectionGuard.read Plain first semantic costs (available _ List.mem_cons_self) guards)
          (fun value member => accepted value (List.mem_cons_of_mem _ member)) row later positive
  cases actual with
  | node reads built =>
    have effects := SourceEqualityProjectionCosts.readAll_effects reads semantic costs available
    have fields := EqualityLeafProjectionPhysical.makeNode_edges _ _ effects.2.1.ready.semantic.1.normal.facts.coherent
      effects.2.1.ready.semantic.1.normal.facts.linked effects.2.2.2
    have ordinary : Ordinary result := by
      simpa only [built] using SourceEqualityRequiredCache.node_ordinary _ _ effects.2.1.ready.semantic.1.normal.facts effects.2.2.2
    apply ordinary_accepted (accept := accept) ordinary
    intro row member positive
    have original : row ∈ canonicalEdges (surviving _) := by simpa only [built] using fields ▸ member
    exact readsAccepted reads semantic costs available guards accepted row
      (List.mem_filter.mp (canonicalEdges_member _ row original)).1 positive

private theorem rows_guards {path index rows before results after}
    (actual : ProjectRows (Symbol := Symbol) (Guard := Guard) path index rows before results after) (semantic : SemanticReady before)
    (costs : CostHeap before) (resident : Edges before rows) (guards : Guards before) : Guards after := by
  induction rows generalizing before results after with
  | nil => cases actual; exact guards
  | cons row rows ih =>
    cases actual with
    | missing _ rest =>
      exact ih rest semantic costs (fun row member => resident row (List.mem_cons_of_mem _ member)) guards
    | selected found first rest =>
      have available := semantic.ready.semantic.1.normal.facts.cached.edges row.entry.key row
        (resident row List.mem_cons_self) _ (select_member found)
      have effects := SourceEqualityProjectionCosts.project_effects first semantic costs available
      exact ih rest effects.2.1 effects.2.2.1
        (fun row member => edge_grows _ _ effects.1.growth row (resident row (List.mem_cons_of_mem _ member)))
        (SourceCurrentConstrainedCapProjectionGuard.node Plain first semantic costs available guards)

private def NodePost (path : List Int) (value : Node) (before : Heap) (result : Node) : Prop :=
  ∀ accept, SemanticReady before → CostHeap before → Available before value → Guards before →
    Safe accept path value → Accepted accept result
private def RowsPost (path : List Int) (index : Int) (rows : List Row) (before : Heap) (results : List Node) : Prop :=
  ∀ accept, SemanticReady before → CostHeap before → Edges before rows → Guards before →
    (∀ row ∈ rows, ∀ child, select row.children index = some child → Safe accept path child) →
    ∀ value ∈ results, Accepted accept value

private theorem project_origins :
    (∀ path value before result after, Project path value before result after → NodePost path value before result) ∧
    (∀ path index rows before results after, ProjectRows path index rows before results after → RowsPost path index rows before results) := by
  have rootCase : ∀ {value state}, NodePost [] value state value := by
    intro value state accept _ _ _ _ safe
    cases safe with
    | empty => exact ordinary_accepted trivial (by intro row member; cases member)
    | plain _ _ annotated => exact plain_accepted annotated
    | root entry rows depth free accepted => exact ordinary_accepted trivial (fun row member _ => accepted row member)
  have emptyCase : ∀ {index path state}, NodePost (index :: path) .empty state .empty := by
    intro index path state accept _ _ _ _ _
    exact ordinary_accepted trivial (by intro row member; cases member)
  have ordinaryCase : ∀ {path index rows before values middle result after entry depth free},
      ProjectRows path index rows before values middle → Union values middle result after →
      RowsPost path index rows before values → NodePost (index :: path) (.node entry rows depth free) before result := by
    intro path index rows before values middle result after entry depth free actual joined ih accept semantic costs available guards safe
    have safeChildren : ∀ row ∈ rows, ∀ child, select row.children index = some child → Safe accept path child := by
      cases safe with
      | plain _ _ annotated =>
        cases annotated with
        | node _ _ _ _ _ children =>
          exact fun row member child found => .plain _ _
            (children child (List.mem_flatMap.mpr ⟨row,member,select_member found⟩))
      | node _ _ _ _ _ _ children => exact children
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have effects := SourceEqualityProjectionCosts.rows_effects actual semantic costs resident
    exact union_accepted joined effects.2.1 effects.2.2.1 effects.2.2.2
      (rows_guards actual semantic costs resident guards)
      (ih accept semantic costs resident guards safeChildren)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (index :: path) exposed middle result after → NodePost (index :: path) exposed middle result →
      NodePost (index :: path) original before result := by
    intro original before exposed middle path index result after recursive head _ ih accept semantic costs available guards safe
    have annotated : Annotated Plain original := by
      cases safe with
      | plain _ _ annotated => exact annotated
      | empty => cases recursive
      | node => cases recursive
    have bounded := SourceCurrentConstrainedCapOpenExposure.head Plain 0 head semantic costs available
      (.plain 0 annotated) (SourceCurrentConstrainedCapGuardNative.stored Plain before guards)
    have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact ih accept effects.2.1 effects.2.2.1 effects.2.2.2
      (SourceCurrentConstrainedCapProjectionGuard.head Plain head semantic costs available guards)
      (.plain _ _ (bounded.2.annotated rfl))
  have nilCase : ∀ {path index state}, RowsPost path index [] state [] := by
    intro path index state accept _ _ _ _ _ value member; cases member
  have missingCase : ∀ {row path index rows before results after}, select row.children index = none →
      ProjectRows path index rows before results after → RowsPost path index rows before results →
      RowsPost path index (row :: rows) before results := by
    intro row path index rows before results after _ _ ih accept semantic costs resident guards safe
    exact ih accept semantic costs (fun row member => resident row (List.mem_cons_of_mem _ member)) guards
      (fun row member child found => safe row (List.mem_cons_of_mem _ member) child found)
  have selectedCase : ∀ {row index child path before result middle rows results after},
      select row.children index = some child → Project path child before result middle →
      ProjectRows path index rows middle results after → NodePost path child before result →
      RowsPost path index rows middle results → RowsPost path index (row :: rows) before (result :: results) := by
    intro row index child path before result middle rows results after found first _ firstIH restIH accept semantic costs resident guards safe
    have available := semantic.ready.semantic.1.normal.facts.cached.edges row.entry.key row
      (resident row List.mem_cons_self) child (select_member found)
    have effects := SourceEqualityProjectionCosts.project_effects first semantic costs available
    have own := firstIH accept semantic costs available guards (safe row List.mem_cons_self child found)
    have later := restIH accept effects.2.1 effects.2.2.1
      (fun row member => edge_grows before middle effects.1.growth row (resident row (List.mem_cons_of_mem _ member)))
      (SourceCurrentConstrainedCapProjectionGuard.node Plain first semantic costs available guards)
      (fun row member child found => safe row (List.mem_cons_of_mem _ member) child found)
    intro value member
    rcases List.mem_cons.mp member with rfl | included
    · exact own
    · exact later value included
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun path value before result _ _ => NodePost path value before result)
      (motive_2 := fun path index rows before results _ _ => RowsPost path index rows before results)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index rows before results after actual
    exact ProjectRows.rec (motive_1 := fun path value before result _ _ => NodePost path value before result)
      (motive_2 := fun path index rows before results _ _ => RowsPost path index rows before results)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- A positive physical projection row follows only original ordinary children after a false primary gate. -/
theorem positive (path : EqualityNormalize.Path) (value : Node) (gateBefore gateAfter before after : Heap)
    (result : Node) (gate : NodeTrace source reaches path value gateBefore false gateAfter)
    (initialSemantic : SemanticReady gateBefore)
    (initialNormal : SourceCurrentRequiredUnionNormal.UnionNormal gateBefore)
    (initialAvailable : Available gateBefore value) (retained : Grows gateAfter before)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (actual : Project (path.map Int.ofNat) value before result after)
    (row : Row) (selected : row ∈ nodeEdges result) (positive : ¬ Plain row.entry.key.constraint) :
    Route (path.map Int.ofNat) value row := by
  have replay := SourceCurrentPrimaryReplay.node_replay source reaches path value gateBefore false gateAfter
    gate initialSemantic initialAvailable
  have safe := safe_gate path value gateBefore before before initialSemantic initialNormal initialAvailable
    semantic available (replay.2.2 before retained)
  have accepted := project_origins.1 _ _ _ _ _ actual _ semantic costs available guards safe
  have effects := SourceEqualityProjectionCosts.project_effects actual semantic costs available
  have finalGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain actual semantic costs available guards
  have read : Read result after (nodeEdges result) after := by
    cases result with
    | empty | node => exact .done 0 rfl
    | reference | union | mu => cases selected
  exact accepted _ _ _ read effects.2.1 effects.2.2.1 effects.2.2.2 finalGuards row selected positive

end Actual
end MicroCFTA.SourceCurrentPositiveProjectionSourceRoute
