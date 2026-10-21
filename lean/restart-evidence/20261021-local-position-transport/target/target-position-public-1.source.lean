import MicroCFTA.SourceCurrentRequiredProjectionOrigins
import MicroCFTA.SourceCurrentRequiredForestPositive
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceCurrentRequiredGuard
import MicroCFTA.SourceCurrentMergePositivePosition
import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound

namespace MicroCFTA.SourceCurrentTargetOperandPositivePosition
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityAnnotationLanguage EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (Origin RowMap ChildMap)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentRequiredGuardOrigins (RowOrigin)
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

private theorem identity_children (values : List Node) : All₂ Origin values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (.identity value) ih

private def RowsPlain (rows : List Row) : Prop :=
  ∀ row ∈ rows, Plain row.entry.key.constraint ∧ ∀ child ∈ row.children, Annotated Plain child

private def ChildrenPlain (values : List Node) : Prop := ∀ value ∈ values, Annotated Plain value

private theorem origin_plain {original prepared : Node} (origin : Origin original prepared) :
    Annotated Plain original → Annotated Plain prepared := by
  apply Origin.rec
    (motive_1 := fun original prepared _ => Annotated Plain original → Annotated Plain prepared)
    (motive_2 := fun originals outputs _ => RowsPlain originals → RowsPlain outputs)
    (motive_3 := fun originals outputs _ => ChildrenPlain originals → ChildrenPlain outputs)
    (t := origin)
  · intro value annotated; exact annotated
  · intro original prepared annotated _; exact annotated
  · intro entry originals level free result ordinary mapped ih annotated
    have rows : RowsPlain originals := fun row member => SourceCurrentHereditaryUnconstrained.node_edge annotated row member
    have outputs := ih rows
    cases result with
    | empty => exact .empty
    | reference | union | mu => cases ordinary
    | node entry edges depth free =>
      exact .node entry edges depth free (fun row member => (outputs row member).1)
        (fun child member => by
          obtain ⟨row,member,inside⟩ := List.mem_flatMap.mp member
          exact (outputs row member).2 child inside)
  · intro originals rows row member; cases member
  · intro originals outputs sourceIndex original output found fields children rest childIH restIH rows row member
    rcases List.mem_cons.mp member with rfl | later
    · have originalPlain := rows original (List.mem_of_getElem? found)
      exact ⟨fields.1 ▸ originalPlain.1,childIH originalPlain.2⟩
    · exact restIH rows row later
  · intro children value member; cases member
  · intro original output originals outputs first rest firstIH restIH children value member
    rcases List.mem_cons.mp member with rfl | later
    · exact firstIH (children original List.mem_cons_self)
    · exact restIH (fun child member => children child (List.mem_cons_of_mem _ member)) value later

private def Anchored (accept : Row → Prop) (row : Row) : Prop :=
  ∃ original, accept original ∧ RowOrigin original row ∧ All₂ Origin original.children row.children

private theorem safe_origin {accept : Row → Prop} {path : List Int} {original prepared : Node}
    (safe : Safe accept path original) (origin : Origin original prepared) :
    Safe (Anchored accept) path prepared := by
  induction path generalizing original prepared with
  | nil =>
    cases origin with
    | identity value =>
      exact safe_map safe (fun row accepted => ⟨row,accepted,⟨rfl,rfl,rfl⟩,identity_children row.children⟩)
    | plain original prepared annotated => exact .plain [] prepared annotated
    | ordinary entry originals level free prepared ordinary mapped =>
      cases safe with
      | plain _ _ annotated => exact .plain [] prepared (origin_plain (.ordinary entry originals level free prepared ordinary mapped) annotated)
      | root _ _ _ _ accepted =>
        cases prepared with
        | empty => exact .empty []
        | reference | union | mu => cases ordinary
        | node entry edges depth free =>
          apply Safe.root entry edges depth free
          intro row member
          obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
          obtain ⟨sourceIndex,sourceRow,original,fields,children⟩ := mapped.indexed position row found
          exact ⟨sourceRow,accepted sourceRow (List.mem_of_getElem? original),fields,children⟩
  | cons index path ih =>
    cases origin with
    | identity value =>
      exact safe_map safe (fun row accepted => ⟨row,accepted,⟨rfl,rfl,rfl⟩,identity_children row.children⟩)
    | plain original prepared annotated => exact .plain _ prepared annotated
    | ordinary entry originals level free prepared ordinary mapped =>
      cases safe with
      | plain _ _ annotated => exact .plain _ prepared (origin_plain (.ordinary entry originals level free prepared ordinary mapped) annotated)
      | node _ _ _ _ _ _ children =>
        cases prepared with
        | empty => exact .empty _
        | reference | union | mu => cases ordinary
        | node entry edges depth free =>
          apply Safe.node entry edges depth free index path
          intro row member child selected
          obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp member
          obtain ⟨sourceIndex,sourceRow,original,fields,related⟩ := mapped.indexed position row found
          obtain ⟨sourceChild,sourceFound,childOrigin⟩ := SourceEqualityProjectionLanguage.all₂_signed related index child selected
          exact ih (children sourceRow (List.mem_of_getElem? original) sourceChild sourceFound) childOrigin

private def RowPosition (row : Row) : List Nat → Prop
  | [] => SourceMemoGate.plain row.entry.key.constraint = false
  | index :: path => ∃ child, row.children[index]? = some child ∧ PositiveAt child path

private def Relevant (row : Row) : Prop := ∃ path, RowPosition row path

private theorem row_origin_position {original row : Row} {path : List Nat}
    (fields : RowOrigin original row) (children : All₂ Origin original.children row.children)
    (positive : RowPosition row path) : RowPosition original path := by
  cases path with
  | nil => simpa only [RowPosition, fields.1] using positive
  | cons index path =>
    obtain ⟨child, found, positive⟩ := positive
    obtain ⟨sourceChild, sourceFound, related⟩ :=
      SourceEqualityProjectionLanguage.all₂_selected children index child found
    exact ⟨sourceChild, sourceFound, SourceCurrentRequiredPositivePosition.origin related positive⟩

private theorem route_position (path : List Nat) {value : Node} {row : Row} {residual : List Nat}
    (route : Route (path.map Int.ofNat) value row) (positive : RowPosition row residual) :
    PositiveAt value (path ++ residual) := by
  induction path generalizing value with
  | nil =>
    cases route with
    | root entry rows depth free position row found =>
      cases residual with
      | nil => exact .root position row found positive
      | cons index rest =>
        obtain ⟨child, chosen, positive⟩ := positive
        exact .child position index row child found chosen positive
  | cons index path ih =>
    cases route with
    | child entry rows depth free position sourceRow found signed child chosen rest =>
      have natural : sourceRow.children[index]? = some child := by
        simpa only [select,Int.ofNat_eq_natCast,
          ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using chosen
      exact .child position index sourceRow child found natural (ih rest)

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
  ∀ before rows after, Read value before rows after → SemanticReady before → Available before value → Guards before → ∀ row ∈ rows, Relevant row → accept row

private theorem plain_accepted {accept : Row → Prop} {value : Node} (annotated : Annotated Plain value) :
    Accepted accept value := by
  intro before rows after actual semantic available guards row member positive
  cases actual with
  | done fuel completed =>
    have bounded := SourceCurrentConstrainedCapOpenExposure.nodeEdges Plain 0 fuel value before
      semantic.ready.semantic semantic.ready.covered available (.plain 0 annotated)
      (SourceCurrentConstrainedCapGuardNative.stored Plain before guards) rows after completed
    obtain ⟨path, positive⟩ := positive
    cases path with
    | nil =>
      have plain := (bounded.2 row member).1
      change SourceMemoGate.plain row.entry.key.constraint = true at plain
      rw [show SourceMemoGate.plain row.entry.key.constraint = false from positive] at plain
      cases plain
    | cons index path =>
      obtain ⟨child, chosen, positive⟩ := positive
      exact False.elim (SourceCurrentRequiredPositivePosition.not_plain positive
        ((bounded.2 row member).2 child (List.mem_of_getElem? chosen)))

private theorem ordinary_read {value : Node} (ordinary : Ordinary value) {before rows after}
    (actual : Read value before rows after) : rows = nodeEdges value := by
  cases value with
  | empty | node =>
    cases actual with
    | done fuel completed => exact (MergedSourceExposure.Result.done.inj completed).1.symm
  | reference | union | mu => cases ordinary

private theorem ordinary_accepted {accept : Row → Prop} {value : Node} (ordinary : Ordinary value)
    (accepted : ∀ row ∈ nodeEdges value, Relevant row → accept row) : Accepted accept value := by
  intro before rows after actual _ _ _ row member positive
  exact accepted row (ordinary_read ordinary actual ▸ member) positive

private theorem union_accepted {accept : Row → Prop} {values before result after}
    (actual : Union values before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (guards : Guards before)
    (accepted : ∀ value ∈ values, Accepted accept value) : Accepted accept result := by
  have readsAccepted : ∀ {values before rows after}, ReadAll values before rows after →
      SemanticReady before → CostHeap before → Values before values → Guards before →
      (∀ value ∈ values, Accepted accept value) → ∀ row ∈ rows, Relevant row → accept row := by
    intro values before rows after actual
    induction actual with
    | nil => intro _ _ _ _ _ row member; cases member
    | @cons value before rows middle values more after first rest ih =>
      intro semantic costs available guards accepted row member positive
      have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      rcases List.mem_append.mp member with here | later
      · exact accepted value List.mem_cons_self _ _ _ first semantic (available _ List.mem_cons_self) guards row here positive
      · exact ih effects.2.1 effects.2.2.1
          (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
          (SourceCurrentConstrainedCapProjectionGuard.read Plain first semantic costs (available _ List.mem_cons_self) guards)
          (fun value member => accepted value (List.mem_cons_of_mem _ member)) row later positive
  cases actual with
  | @node edges middle result after reads built =>
    have effects := SourceEqualityProjectionCosts.readAll_effects reads semantic costs available
    have fields := EqualityLeafProjectionPhysical.makeNode_edges _ _ effects.2.1.ready.semantic.1.normal.facts.coherent
      effects.2.1.ready.semantic.1.normal.facts.linked effects.2.2.2
    have ordinary : Ordinary result := by
      simpa only [built] using SourceEqualityRequiredCache.node_ordinary _ _ effects.2.1.ready.semantic.1.normal.facts effects.2.2.2
    apply ordinary_accepted (accept := accept) ordinary
    intro row member positive
    have original : row ∈ canonicalEdges (surviving edges) := by
      rw [built] at fields
      exact fields ▸ member
    exact readsAccepted reads semantic costs available guards accepted row
      (List.mem_filter.mp (canonicalEdges_member _ row original)).1 positive

private theorem rows_guards {path index rows before results after}
    (actual : @ProjectRows Symbol Guard _ path index rows before results after) (semantic : SemanticReady before)
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

/-- A positive prepared projection retains the original natural child path. -/
theorem project (path : List Nat) (original prepared : Node)
    (gateBefore gateAfter before after : Heap) (result : Node)
    (origin : Origin original prepared)
    (gate : NodeTrace source reaches path original gateBefore false gateAfter)
    (initialSemantic : SemanticReady gateBefore)
    (initialNormal : SourceCurrentRequiredUnionNormal.UnionNormal gateBefore)
    (initialAvailable : Available gateBefore original)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before prepared)
    (guards : Guards before) (actual : Project (path.map Int.ofNat) prepared before result after)
    {residual : List Nat} (positive : PositiveAt result residual) :
    PositiveAt original (path ++ residual) := by
  cases path with
  | nil =>
    cases actual
    exact SourceCurrentRequiredPositivePosition.origin origin positive
  | cons index path =>
    have safe := safe_gate (index :: path) original gateBefore gateBefore gateAfter initialSemantic initialNormal
      initialAvailable initialSemantic initialAvailable gate
    have preparedSafe := safe_origin safe origin
    have accepted := project_origins.1 _ _ _ _ _ actual _ semantic costs available guards preparedSafe
    have effects := SourceEqualityProjectionCosts.project_effects actual semantic costs available
    have finalGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain actual semantic costs available guards
    have ordinary := project_ordinary actual semantic costs available (by simp)
    cases positive with
    | root rowIndex row selected nonplain =>
      obtain ⟨sourceRow, route, fields, children⟩ :=
        accepted after _ after (.done 0 rfl) effects.2.1 effects.2.2.2 finalGuards row
          (List.mem_of_getElem? selected) ⟨[], nonplain⟩
      exact route_position (index :: path) route (row_origin_position fields children nonplain)
    | child rowIndex childIndex row child selected chosen rest =>
      obtain ⟨sourceRow, route, fields, children⟩ :=
        accepted after _ after (.done 0 rfl) effects.2.1 effects.2.2.2 finalGuards row
          (List.mem_of_getElem? selected) ⟨childIndex :: _, child, chosen, rest⟩
      exact route_position (index :: path) route
        (row_origin_position fields children ⟨child, chosen, rest⟩)
    | member => cases ordinary

end Actual

open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentMergePositivePosition (Support)

/-- An actual Required and target operand return retains its fixed original slot and full positive path. -/
theorem operand [symbolEq : DecidableEq Symbol] [edgeEq : DecidableEq (EdgeKey Symbol Guard)]
    {width requiredFuel requiredReadFuel projectionFuel readFuel mergeFuel selectionFuel : Nat}
    {selected : EqualityNormalize.Constraints} {originals prepared : List Node}
    {scanHeap preparedHeap : Heap} {index : Nat} {path residual : List Nat}
    {chosenClass : EqualityNormalize.Class}
    {before after : SourceEqualityNativeDemand.State width}
    {memo saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard} {result : Node}
    (required : SourceEqualityRequiredExecution.requireAll requiredFuel requiredReadFuel
      (SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap)
    (semantic : SemanticReady scanHeap) (normal : SourceCurrentRequiredUnionNormal.UnionNormal scanHeap)
    (costs : CostHeap scanHeap) (available : Values scanHeap originals) (guards : Guards scanHeap)
    (primary : ∀ paths ∈ selected, ClassTrace source reaches originals paths scanHeap false scanHeap)
    (chosen : chosenClass ∈ selected) (included : index :: path ∈ chosenClass)
    (sameHeap : before.native.machine.heap = preparedHeap)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (support : Support memo)
    (actual : SourceCurrentAllocatedTargetWorker.operand projectionFuel readFuel mergeFuel selectionFuel
      ((index :: path).map Int.ofNat) prepared before memo = .done result after saved)
    (positive : PositiveAt result residual) :
    Support saved ∧ ∃ original, originals[index]? = some original ∧ PositiveAt original (path ++ residual) := by
  have sameEdge : edgeEq = SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint :=
    Subsingleton.elim _ _
  cases sameEdge
  letI : DecidableEq (EdgeKey Symbol Guard) :=
    SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint
  have sameSymbol : symbolEq = @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
      instDecidableEqString FormulaExecutable.formulaDecidableEq := Subsingleton.elim _ _
  cases sameSymbol
  letI : DecidableEq Symbol := @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
    instDecidableEqString FormulaExecutable.formulaDecidableEq
  have requiredEffects := SourceCurrentRequiredHeapEffects.requireAll (fun _ => True)
    requiredFuel requiredReadFuel (SourceEqualitySelectedRequired.paths selected) originals prepared scanHeap preparedHeap
    required semantic costs (fun _ _ _ => trivial) available
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff
    (SourceEqualitySelectedRequired.paths selected) originals scanHeap prepared preparedHeap).mpr
      ⟨requiredFuel, requiredReadFuel, required⟩
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected) with
  | node entries =>
    simp only [compiled] at graph
    have domain := SourceCurrentRequiredPrimaryExposure.selected_domain originals selected scanHeap
      semantic normal available primary entries compiled
    have safe : SourceCurrentRequiredRowOrigins.ChildrenSafe entries 0 originals := by
      intro offset needed selectedNeeded value atOffset
      exact domain offset needed (by simpa only [Nat.zero_add] using selectedNeeded) value atOffset
    have related : All₂ Origin originals prepared :=
      SourceCurrentRequiredRowOrigins.children graph semantic costs available guards safe
    have preparedGuards := SourceCurrentRequiredGuard.children Plain graph semantic costs available guards
    obtain ⟨projected,middle,current,projectionDone,mergeDone⟩ :=
      (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
    obtain ⟨heap,forest,shape,sameMemo⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound
      projectionFuel readFuel ((index :: path).map Int.ofNat) prepared before memo projected middle current projectionDone
    subst current
    have beforeSemantic : SemanticReady before.native.machine.heap := sameHeap ▸ requiredEffects.2.1
    have beforeCosts : CostHeap before.native.machine.heap := sameHeap ▸ requiredEffects.2.2.1
    have beforeValues : Values before.native.machine.heap prepared := sameHeap ▸ requiredEffects.2.2.2.2
    have facts := SourceEqualityProjectionCosts.forest_effects forest beforeSemantic beforeCosts beforeValues
    have middleHeap : middle.native.machine.heap = heap := by rw [shape]; rfl
    have currentSemantic : SemanticReady middle.native.machine.heap := by simpa only [middleHeap] using facts.2.1
    have currentCosts : CostHeap middle.native.machine.heap := by simpa only [middleHeap] using facts.2.2.1
    have currentStored : SourceCurrentMemoMergeEffects.Stored middle.native.machine.heap memo := by
      simpa only [middleHeap] using stored.grows facts.1
    have currentAvailable : Available middle.native.machine.heap projected := by simpa only [middleHeap] using facts.2.2.2
    cases called : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear
        mergeFuel selectionFuel projected (physical middle) memo with
    | failed =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
    | done output final current =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
      have merged := SourceCurrentMergePositivePosition.allocated SourceCurrentAllocatedMerge.literalClear called
        currentSemantic currentCosts currentStored support currentAvailable
      have projectedPositive := merged.2.2.2.2 residual positive
      refine ⟨merged.2.2.1, ?_⟩
      cases forest with
      | missing absent => cases projectedPositive
      | selected found actualProject =>
        have natural := found
        simp only [select,Int.ofNat_eq_natCast,
          ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] at natural
        obtain ⟨original, originalFound, origin⟩ :=
          SourceEqualityProjectionLanguage.all₂_selected related index _ natural
        have gatePath := SourceCurrentRequiredPrimaryExposure.false_class_paths originals chosenClass scanHeap scanHeap
          (primary chosenClass chosen) semantic available scanHeap (grows_refl _) (index :: path) included
        have gate : NodeTrace source reaches path original scanHeap false scanHeap := by
          cases gatePath with
          | child traced => exact SourceCurrentRequiredPrimaryExposure.false_selected traced originalFound
        refine ⟨original, originalFound, ?_⟩
        exact project path original _ scanHeap scanHeap before.native.machine.heap heap projected origin gate
          semantic normal (available _ (List.mem_of_getElem? originalFound)) beforeSemantic beforeCosts
          (beforeValues _ (select_member found)) (sameHeap ▸ preparedGuards) actualProject projectedPositive

end MicroCFTA.SourceCurrentTargetOperandPositivePosition

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 16384
set_option maxHeartbeats 0

#check @MicroCFTA.SourceCurrentTargetOperandPositivePosition.project
#print MicroCFTA.SourceCurrentTargetOperandPositivePosition.project
#print axioms MicroCFTA.SourceCurrentTargetOperandPositivePosition.project

#check @MicroCFTA.SourceCurrentTargetOperandPositivePosition.operand
#print MicroCFTA.SourceCurrentTargetOperandPositivePosition.operand
#print axioms MicroCFTA.SourceCurrentTargetOperandPositivePosition.operand

