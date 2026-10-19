import MicroCFTA.SourceCurrentClassFoldRowOrigins
import MicroCFTA.SourceCurrentRequiredProjectionOrigins
import MicroCFTA.SourceCurrentProjectionReadSpine

/-!
# Observation continuations through actual class node edits

The original false gate and Required origin construct path safety.
A selected continuation follows the actual edit, projection, and row read.
Native leaf and Head cuts retain the remaining execution.
-/
namespace MicroCFTA.SourceCurrentClassObservationSpines
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityAnnotationLanguage EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (Origin RowMap ChildMap)
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
  ∀ before rows after, Read value before rows after → SemanticReady before → Available before value → Guards before → ∀ row ∈ rows, ¬ Plain row.entry.key.constraint → accept row

private theorem plain_accepted {accept : Row → Prop} {value : Node} (annotated : Annotated Plain value) :
    Accepted accept value := by
  intro before rows after actual semantic available guards row member positive
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
  intro before rows after actual _ _ _ row member positive
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


/-- An ordinary projection retains its selected child and its actual row-read interval. -/
structure ProjectionFrame (index : Int) (path : List Int) (edges : List Row)
    (before : Heap) (result : Node) (after : Heap) (row : Row) where
  /-- The actual values witness. -/
  values : List Node
  /-- The actual middle witness. -/
  middle : Heap
  /-- The actual allRows witness. -/
  allRows : List Row
  /-- The actual unionMiddle witness. -/
  unionMiddle : Heap
  /-- The actual projects witness. -/
  projects : ProjectRows path index edges before values middle
  /-- The actual reads witness. -/
  reads : ReadAll values middle allRows unionMiddle
  /-- The actual built witness. -/
  built : run (makeNode allRows) unionMiddle = (result,after)
  /-- The actual rawIndex witness. -/
  rawIndex : Nat
  /-- The actual raw witness. -/
  raw : allRows[rawIndex]? = some row
  /-- The actual operandIndex witness. -/
  operandIndex : Nat
  /-- The actual operand witness. -/
  operand : Node
  /-- The actual operand selection witness. -/
  operandSelected : values[operandIndex]? = some operand
  /-- The actual earlierRows witness. -/
  earlierRows : List Row
  /-- The actual selectedRows witness. -/
  selectedRows : List Row
  /-- The actual laterRows witness. -/
  laterRows : List Row
  /-- The actual readStart witness. -/
  readStart : Heap
  /-- The actual readFinish witness. -/
  readFinish : Heap
  /-- The actual readPrefix witness. -/
  readPrefix : ReadAll (values.take operandIndex) middle earlierRows readStart
  /-- The actual operand read witness. -/
  operandRead : Read operand readStart selectedRows readFinish
  /-- The actual readSuffix witness. -/
  readSuffix : ReadAll (values.drop (operandIndex+1)) readFinish laterRows unionMiddle
  /-- The actual parts witness. -/
  parts : allRows = earlierRows ++ selectedRows ++ laterRows
  /-- The actual readIndex witness. -/
  readIndex : Nat
  /-- The actual read selection witness. -/
  readSelected : selectedRows[readIndex]? = some row
  /-- The actual sourceIndex witness. -/
  sourceIndex : Nat
  /-- The actual sourceRow witness. -/
  sourceRow : Row
  /-- The actual child witness. -/
  child : Node
  /-- The actual start witness. -/
  start : Heap
  /-- The actual finish witness. -/
  finish : Heap
  /-- The actual source selection witness. -/
  sourceSelected : edges[sourceIndex]? = some sourceRow
  /-- The actual child selection witness. -/
  childSelected : select sourceRow.children index = some child
  /-- The actual projectPrefix witness. -/
  projectPrefix : ProjectRows path index (edges.take sourceIndex) before (values.take operandIndex) start
  /-- The actual call witness. -/
  call : Project path child start operand finish
  /-- The actual projectSuffix witness. -/
  projectSuffix : ProjectRows path index (edges.drop (sourceIndex+1)) finish (values.drop (operandIndex+1)) middle
  /-- The actual rest witness. -/
  rest : SourceCurrentProjectionReadSpine.Spine call operandRead readIndex row

open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] {width : Nat}

/-- A surviving row retains the actual raw reconstruction and ordered child calls. -/
structure Reconstruction (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries edges before rebuilt middle}
    (actual : EditRows (width := width) record originals entries edges before rebuilt middle)
    (memos final : Memos) (heap : Heap) (parent : Row) where
  /-- The actual sourceRow witness. -/
  sourceRow : Row
  /-- The actual index witness. -/
  index : Nat
  /-- The actual start witness. -/
  start : SharedState width
  /-- The actual rowMiddle witness. -/
  rowMiddle : SharedState width
  /-- The actual values witness. -/
  values : List Node
  /-- The actual rowHeap witness. -/
  rowHeap : Heap
  /-- The actual startInventory witness. -/
  startInventory : Inventory
  /-- The actual middleInventory witness. -/
  middleInventory : Inventory
  /-- The actual rowMemos witness. -/
  rowMemos : Memos
  /-- The actual rowFinal witness. -/
  rowFinal : Memos
  /-- The actual earlier witness. -/
  earlier : EditRows record originals entries (edges.take index) before (rebuilt.take index) start
  /-- The actual children witness. -/
  children : EditChildren record originals entries 0 sourceRow.children start values rowMiddle
  /-- The actual source selection witness. -/
  sourceSelected : edges[index]? = some sourceRow
  /-- The actual raw selection witness. -/
  rawSelected : rebuilt[index]? = some parent
  /-- The actual prefix reads witness. -/
  prefixReads : RowsReads formulas solver base earlier memos rowMemos
  /-- The actual child reads witness. -/
  childReads : ChildrenReads formulas solver base children rowMemos rowFinal
  /-- The actual valid witness. -/
  valid : EndpointMemoGateTrace.Valid start.checked.native.machine.heap rowMemos
  /-- The actual edgeBuilt witness. -/
  edgeBuilt : run (makeEdge sourceRow.entry.key.symbol sourceRow.entry.key.constraint values)
    rowMiddle.checked.native.machine.heap = (parent,rowHeap)
  /-- The actual symbol witness. -/
  symbol : parent.entry.key.symbol = sourceRow.entry.key.symbol
  /-- The actual guard witness. -/
  guard : parent.entry.key.constraint = sourceRow.entry.key.constraint
  /-- The actual exactChildren witness. -/
  exactChildren : parent.children = values
  /-- The actual start readiness witness. -/
  startReady : SharedReady formulas solver startInventory record originals base start
  /-- The actual middle readiness witness. -/
  middleReady : SharedReady formulas solver middleInventory record originals base rowMiddle
  /-- The actual start history witness. -/
  startHistory : History start.checked
  /-- The actual middle history witness. -/
  middleHistory : History rowMiddle.checked
  /-- The actual start growth witness. -/
  startGrowth : Grows start.checked.native.machine.heap heap
  /-- The actual middle growth witness. -/
  middleGrowth : Grows rowMiddle.checked.native.machine.heap heap
  /-- The actual row growth witness. -/
  rowGrowth : Grows rowHeap heap
  /-- The actual live witness. -/
  live : EqualityLeafProjectionPhysical.dead parent = false
  /-- The actual slices witness. -/
  slices : ∀ childIndex child, values[childIndex]? = some child →
    SourceCurrentSharedEditChildLineage.Slice formulas solver base record originals entries 0
      sourceRow.children start values rowMiddle rowMemos rowFinal childIndex child

/-- A selected observation follows actual edits. True marks a native or Head cut. -/
inductive Spine (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : SourceEqualityClassOrder.Record} → {originals : List Node} →
    {edits : Edits EqualityNormalize.Path} → {input : Node} → {before : SharedState width} →
    {result : Node} → {after : SharedState width} →
    EditNode (width := width) record originals edits input before result after →
    {path : List Int} → {projectBefore : Heap} → {projected : Node} → {projectAfter : Heap} → Project path result projectBefore projected projectAfter →
    {reader : Heap} → {observed : List Row} → {readAfter : Heap} → Read projected reader observed readAfter → Nat → Row → Bool → Prop where
  /-- The native leaf retains its complete remaining projection and terminal read. -/
  | leaf {record originals target input before result after memos final}
      {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals target input before result after}
      (reads : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
      (history : History before.checked)
      {path projectBefore projected projectAfter}
      {project : Project path result projectBefore projected projectAfter}
      {reader observed readAfter} {read : Read projected reader observed readAfter} {position row}
      (remaining : SourceCurrentProjectionReadSpine.Spine project read position row) :
      Spine formulas solver base (.leaf actual) project read position row true
  /-- The Head cut retains the actual body edit and observes its returned value. -/
  | head {record originals entries input before exposed heap result after memos current final}
      {recursive : SourceEqualityRequiredGraph.Recursive input}
      {head : SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) result after}
      (headRead : SourceCurrentRequiredQueryMemos.HeadReads head memos current)
      (headGlobal : SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos current)
      (bodyRead : NodeReads formulas solver base body current final) (history : History before.checked)
      {path projectBefore projected projectAfter}
      {project : Project path result projectBefore projected projectAfter}
      {reader observed readAfter} {read : Read projected reader observed readAfter} {position row}
      (remaining : SourceCurrentProjectionReadSpine.Spine project read position row) :
      Spine formulas solver base (.recursive recursive head body) project read position row true
  /-- An empty projection path observes one exact canonical reconstruction. -/
  | root {record originals entries edges before rebuilt middle result heap entry depth free memos final}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (result,heap)}
      (readRows : RowsReads formulas solver base actual memos final)
      {state reader observed readAfter} (read : Read result reader observed readAfter)
      (position : Nat) (row : Row) (selected : observed[position]? = some row)
      (canonical : (nodeEdges result)[position]? = some row)
      (reconstruction : Reconstruction formulas solver base actual memos final heap row) :
      Spine formulas solver base (.ordinary (entry := entry) (depth := depth) (free := free) actual built)
        (Project.root (state := state)) read position row false
  /-- An unchanged child retains its actual projection and ordered edit slice. -/
  | unchanged {record originals entries edges before rebuilt middle result heap entry depth free memos final}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (result,heap)}
      (readRows : RowsReads formulas solver base actual memos final)
      {index path projectBefore projected projectAfter outEntry outEdges outDepth outFree}
      (shape : result = .node outEntry outEdges outDepth outFree)
      {project : Project (index :: path) result projectBefore projected projectAfter}
      {reader observed readAfter} {read : Read projected reader observed readAfter} {position row}
      (remaining : SourceCurrentProjectionReadSpine.Spine project read position row)
      (frame : ProjectionFrame index path outEdges projectBefore projected projectAfter row)
      (reconstruction : Reconstruction formulas solver base actual memos final heap frame.sourceRow)
      (childIndex : Nat) (chosen : frame.sourceRow.children[childIndex]? = some frame.child)
      (originalChild : Node) (sourceChosen : reconstruction.sourceRow.children[childIndex]? = some originalChild)
      (same : frame.child = originalChild)
      (slice : SourceCurrentSharedEditChildLineage.Slice formulas solver base record originals entries 0
        reconstruction.sourceRow.children reconstruction.start reconstruction.values reconstruction.rowMiddle
        reconstruction.rowMemos reconstruction.rowFinal childIndex frame.child)
      (absent : SourceEqualityNeededMap.lookup (childIndex : Int) entries = none) :
      Spine formulas solver base (.ordinary (entry := entry) (depth := depth) (free := free) actual built)
        project read position row false
  /-- A selected child follows the same actual projected operand and row-read interval. -/
  | selected {record originals entries edges before rebuilt middle result heap entry depth free memos final}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (result,heap)}
      (readRows : RowsReads formulas solver base actual memos final)
      {index path projectBefore projected projectAfter outEntry outEdges outDepth outFree}
      (shape : result = .node outEntry outEdges outDepth outFree)
      {project : Project (index :: path) result projectBefore projected projectAfter}
      {reader observed readAfter} {read : Read projected reader observed readAfter} {position row}
      (remaining : SourceCurrentProjectionReadSpine.Spine project read position row)
      (frame : ProjectionFrame index path outEdges projectBefore projected projectAfter row)
      (reconstruction : Reconstruction formulas solver base actual memos final heap frame.sourceRow)
      (childIndex : Nat) (chosen : frame.sourceRow.children[childIndex]? = some frame.child)
      (originalChild : Node) (sourceChosen : reconstruction.sourceRow.children[childIndex]? = some originalChild)
      {edits start finish current saved}
      (call : EditNode record originals edits originalChild start frame.child finish)
      (found : SourceEqualityNeededMap.lookup (childIndex : Int) entries = some edits)
      (earlier : EditChildren record originals entries 0 (reconstruction.sourceRow.children.take childIndex)
        reconstruction.start (reconstruction.values.take childIndex) start)
      (later : EditChildren record originals entries (childIndex+1) (reconstruction.sourceRow.children.drop (childIndex+1))
        finish (reconstruction.values.drop (childIndex+1)) reconstruction.rowMiddle)
      (prefixRead : ChildrenReads formulas solver base earlier reconstruction.rowMemos current)
      (callRead : NodeReads formulas solver base call current saved)
      (suffixRead : ChildrenReads formulas solver base later saved reconstruction.rowFinal)
      {cut : Bool} (rest : Spine formulas solver base call frame.call frame.operandRead frame.readIndex row cut) :
      Spine formulas solver base (.ordinary (entry := entry) (depth := depth) (free := free) actual built)
        project read position row cut


private theorem guards_before {before after : Heap} (growth : Grows before after) (guards : Guards after) :
    Guards before := by
  intro key entry body depth ordinary present
  exact guards key entry body depth ordinary (growth.2 key _ present)

private def Fields (accept : Row → Prop) (row : Row) : Prop :=
  ∃ original, accept original ∧ RowOrigin original row

private theorem reconstruction_fields {formulas solver base record originals entries edges before rebuilt middle}
    {actual : EditRows (width := width) record originals entries edges before rebuilt middle}
    {memos final heap parent} (receipt : Reconstruction formulas solver base actual memos final heap parent) :
    RowOrigin receipt.sourceRow parent :=
  ⟨receipt.symbol,receipt.guard,by rw [receipt.exactChildren]; exact children_length receipt.children⟩

private theorem reconstruct {formulas solver base record originals entries edges before rebuilt middle memos final value heap}
    {actual : EditRows (width := width) record originals entries edges before rebuilt middle}
    (reads : RowsReads formulas solver base actual memos final)
    (built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value,heap))
    (inventory : Inventory) (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SharedReady formulas solver inventory record originals base before)
    (resident : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    {parent : Row} (selected : parent ∈ nodeEdges value) :
    Nonempty (Reconstruction formulas solver base actual memos final heap parent) := by
  obtain ⟨original,_,receipt⟩ := SourceCurrentClassFoldRowOrigins.rebuild reads built inventory populated allowed
    ready resident safe valid history selected
  obtain ⟨_,index,start,rowMiddle,values,rowHeap,startInventory,middleInventory,rowMemos,rowFinal,
    earlier,children,sourceSelected,rawSelected,prefixReads,childReads,valid,edgeBuilt,symbol,guard,exactChildren,
    startReady,middleReady,startHistory,middleHistory,startGrowth,middleGrowth,rowGrowth,live,slices⟩ := receipt
  exact ⟨⟨original,index,start,rowMiddle,values,rowHeap,startInventory,middleInventory,rowMemos,rowFinal,
    earlier,children,sourceSelected,rawSelected,prefixReads,childReads,valid,edgeBuilt,symbol,guard,exactChildren,
    startReady,middleReady,startHistory,middleHistory,startGrowth,middleGrowth,rowGrowth,live,slices⟩⟩

private theorem root_safe {accept : Row → Prop} {entry edges depth free}
    (safe : Safe accept [] (.node entry edges depth free)) {row : Row} (member : row ∈ edges)
    (positive : ¬ Plain row.entry.key.constraint) : accept row := by
  cases safe with
  | root _ _ _ _ accepted => exact accepted row member
  | plain _ _ annotated => exact False.elim (positive (SourceCurrentHereditaryUnconstrained.node_edge annotated row member).1)

private theorem child_safe {accept : Row → Prop} {entry edges depth free index path}
    (safe : Safe accept (index :: path) (.node entry edges depth free)) {row : Row} (member : row ∈ edges)
    {child : Node} (chosen : select row.children index = some child) : Safe accept path child := by
  cases safe with
  | node _ _ _ _ _ _ children => exact children row member child chosen
  | plain _ _ annotated =>
    exact .plain _ _ ((SourceCurrentHereditaryUnconstrained.node_edge annotated row member).2 child (select_member chosen))

private theorem signed_lookup {values : List Node} {index : Int} {child : Node}
    (found : select values index = some child) :
    index = Int.ofNat index.toNat ∧ values[index.toNat]? = some child := by
  have nonnegative : ¬ index < 0 := by
    intro negative
    simp [select,negative] at found
  exact ⟨(Int.toNat_of_nonneg (Int.not_lt.mp nonnegative)).symm,by simpa only [select,if_neg nonnegative] using found⟩

private def NodeLaw (path : List Int) : Prop :=
  ∀ {formulas solver base record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after},
    NodeReads formulas solver base actual memos final →
    ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    SourceCurrentEditDomains.Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos →
    History before.checked → ∀ accept, Safe accept path input →
    ∀ {projectBefore projected projectAfter} (project : Project path result projectBefore projected projectAfter),
    SemanticReady projectBefore → CostHeap projectBefore → Available projectBefore result →
    Grows after.checked.native.machine.heap projectBefore →
    ∀ {reader observed readAfter} (read : Read projected reader observed readAfter),
    SemanticReady reader → Keeps projectAfter reader → Guards reader →
    ∀ position row, observed[position]? = some row → ¬ Plain row.entry.key.constraint →
    ∃ cut, Spine formulas solver base actual project read position row cut ∧ (cut = false → Fields accept row)


end Actual
end MicroCFTA.SourceCurrentClassObservationSpines
