import MicroCFTA.SourceCurrentRequiredPositivePosition
import MicroCFTA.SourceCurrentProjectionReadSpine
import MicroCFTA.SourceCurrentRecursivePlainRead
import MicroCFTA.SourceCurrentConstrainedCapNativeScope

/-! # Positive positions through actual capped projection and selected reads -/
namespace MicroCFTA.SourceCurrentCappedProjectionPositivePosition
open InternedRecordCoherence
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentRequiredPositivePosition (PositiveAt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private def RowPositive (row : Row) : List Nat → Prop
  | [] => SourceMemoGate.plain row.entry.key.constraint = false
  | index :: path => ∃ child, row.children[index]? = some child ∧ PositiveAt child path

private theorem row_not_plain {row path} (positive : RowPositive row path)
    (annotated : SourceCurrentHereditaryConstructors.Edge Plain row) : False := by
  cases path with
  | nil =>
      have same : SourceMemoGate.plain row.entry.key.constraint = true := annotated.1
      rw [positive] at same
      cases same
  | cons index path =>
      obtain ⟨child,chosen,rest⟩ := positive
      exact rest.not_plain (annotated.2 child (List.mem_of_getElem? chosen))

private theorem node_row {entry rows depth free row path} (member : row ∈ rows)
    (positive : RowPositive row path) : PositiveAt (.node entry rows depth free) path := by
  obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
  cases path with
  | nil => exact .root index row selected positive
  | cons childIndex path =>
      obtain ⟨child,chosen,rest⟩ := positive
      exact .child index childIndex row child selected chosen rest

private theorem prepend_done (result : MergedSourceExposure.Result Symbol Guard) (leading rows : List Row)
    (after : Heap) (done : result.prepend leading = .done rows after) :
    ∃ suffix, result = .done suffix after ∧ rows = leading ++ suffix := by
  cases result with
  | done suffix state => cases done; exact ⟨suffix,rfl,rfl⟩
  | unresolved | pending | exhausted => cases done

private theorem canonical_done (result : MergedSourceExposure.Result Symbol Guard) (rows : List Row)
    (after : Heap) (done : result.canonical = .done rows after) :
    ∃ original, result = .done original after ∧ rows = canonicalEdges original := by
  cases result with
  | done original state => cases done; exact ⟨original,rfl,rfl⟩
  | unresolved | pending | exhausted => cases done

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem collect_positive (capDepth fuel : Nat) (state : Heap)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state) (covered : Covered [] state)
    (seen : List Nat) (pending : List Node) (inputs : Values state pending)
    (caps : ∀ value ∈ pending, Cap Plain capDepth value) (stored : MuStored Plain state)
    (rows : List Row) (after : Heap)
    (done : MergedFreshOrdinaryExposure.collect fuel state seen pending = .done rows after) :
    ∀ row ∈ rows, ∀ path, RowPositive row path → ∃ value ∈ pending, PositiveAt value path := by
  induction fuel generalizing state seen pending rows after with
  | zero => cases pending <;> cases done; intro row impossible; cases impossible
  | succ fuel ih =>
    cases pending with
    | nil => cases done; intro row impossible; cases impossible
    | cons value rest =>
      intro row member path positive
      have available := inputs value List.mem_cons_self
      have bounded := caps value List.mem_cons_self
      have restInputs : Values state rest := fun child inside => inputs child (List.mem_cons_of_mem _ inside)
      have restCaps : ∀ child ∈ rest, Cap Plain capDepth child := fun child inside => caps child (List.mem_cons_of_mem _ inside)
      cases value with
      | empty =>
          obtain ⟨child,inside,found⟩ := ih state semantic covered seen rest restInputs restCaps stored rows after done row member path positive
          exact ⟨child,List.mem_cons_of_mem _ inside,found⟩
      | reference => cases done
      | node entry originals depth free =>
          obtain ⟨suffix,returned,same⟩ := prepend_done _ originals rows after done
          rcases List.mem_append.mp (same ▸ member) with here | later
          · exact ⟨_,List.mem_cons_self,node_row here positive⟩
          · obtain ⟨child,inside,found⟩ := ih state semantic covered seen rest restInputs restCaps stored suffix after returned row later path positive
            exact ⟨child,List.mem_cons_of_mem _ inside,found⟩
      | union entry members depth free =>
          by_cases visited : entry.identity ∈ seen
          · have tail : MergedFreshOrdinaryExposure.collect fuel state seen rest = .done rows after := by simpa only [MergedFreshOrdinaryExposure.collect,visited,↓reduceIte] using done
            obtain ⟨child,inside,found⟩ := ih state semantic covered seen rest restInputs restCaps stored rows after tail row member path positive
            exact ⟨child,List.mem_cons_of_mem _ inside,found⟩
          · have nextInputs : Values state (members ++ rest) := by
              intro child inside
              rcases List.mem_append.mp inside with here | later
              · exact available.children child here
              · exact restInputs child later
            have nextCaps : ∀ child ∈ members ++ rest, Cap Plain capDepth child := by
              intro child inside
              rcases List.mem_append.mp inside with here | later
              · exact SourceCurrentConstrainedCap.union_member bounded child here
              · exact restCaps child later
            have tail : MergedFreshOrdinaryExposure.collect fuel state (entry.identity :: seen) (members ++ rest) = .done rows after := by simpa only [MergedFreshOrdinaryExposure.collect,visited,↓reduceIte] using done
            obtain ⟨child,inside,found⟩ := ih state semantic covered _ _ nextInputs nextCaps stored rows after tail row member path positive
            rcases List.mem_append.mp inside with here | later
            · obtain ⟨index,chosen⟩ := List.mem_iff_getElem?.mp here
              exact ⟨_,List.mem_cons_self,.member index child chosen found⟩
            · exact ⟨child,List.mem_cons_of_mem _ later,found⟩
      | mu entry body depth ordinary =>
          by_cases visited : entry.identity ∈ seen
          · have tail : MergedFreshOrdinaryExposure.collect fuel state seen rest = .done rows after := by simpa only [MergedFreshOrdinaryExposure.collect,visited,↓reduceIte] using done
            obtain ⟨child,inside,found⟩ := ih state semantic covered seen rest restInputs restCaps stored rows after tail row member path positive
            exact ⟨child,List.mem_cons_of_mem _ inside,found⟩
          · have checked := SourceCurrentHereditaryConstruction.unfold Plain (.mu entry body depth ordinary) state semantic.1.normal.facts available (SourceCurrentConstrainedCapNativeScope.mu_annotated bounded) stored
            obtain ⟨result,middle,unfolded,context,heap,nextCovered,resultAvailable,growth,history⟩ := InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary) state semantic.1 available semantic.2 covered
            have nextStore : MuStored Plain middle := by simpa only [unfolded,InternedNestedConstruction.Outcome.state] using checked.stored
            have resultPlain := checked.result result middle unfolded
            have nextInputs : Values middle (result :: rest) := by
              intro child inside
              rcases List.mem_cons.mp inside with rfl | later
              · exact resultAvailable
              · exact (restInputs child later).grows state middle growth history
            have nextCaps : ∀ child ∈ result :: rest, Cap Plain capDepth child := by
              intro child inside
              rcases List.mem_cons.mp inside with rfl | later
              · exact .plain capDepth resultPlain
              · exact restCaps child later
            have tail : MergedFreshOrdinaryExposure.collect fuel middle (entry.identity :: seen) (result :: rest) = .done rows after := by simpa only [MergedFreshOrdinaryExposure.collect,visited,↓reduceIte,unfolded] using done
            obtain ⟨child,inside,found⟩ := ih middle ⟨context,heap⟩ nextCovered _ _ nextInputs nextCaps nextStore rows after tail row member path positive
            rcases List.mem_cons.mp inside with rfl | later
            · exact False.elim (found.not_plain resultPlain)
            · exact ⟨child,List.mem_cons_of_mem _ later,found⟩

private theorem read_positive {value before rows after} (read : Read value before rows after)
    (semantic : SemanticReady before) (available : Available before value) (guards : Guards before)
    (capDepth : Nat) (bounded : Cap Plain capDepth value) (row : Row) (member : row ∈ rows)
    (path : List Nat) (positive : RowPositive row path) : PositiveAt value path := by
  cases read with
  | done fuel completed =>
    have stored := SourceCurrentConstrainedCapGuardNative.stored Plain before guards
    cases value with
    | empty | reference => cases completed; cases member
    | node entry originals depth free => cases completed; exact node_row member positive
    | mu entry body depth ordinary =>
        have annotations := SourceCurrentConstrainedCapOpenExposure.nodeEdges Plain 0 fuel (.mu entry body depth ordinary) before semantic.ready.semantic semantic.ready.covered available
          (.plain 0 (SourceCurrentConstrainedCapNativeScope.mu_annotated bounded)) stored rows after completed
        exact False.elim (row_not_plain positive (annotations.2 row member))
    | union entry members depth free =>
        obtain ⟨original,raw,same⟩ := canonical_done _ rows after completed
        obtain ⟨value,inside,found⟩ := collect_positive capDepth fuel before semantic.ready.semantic semantic.ready.covered [] [_]
          (by intro value inside; exact (List.mem_singleton.mp inside) ▸ available)
          (by intro value inside; exact (List.mem_singleton.mp inside) ▸ bounded) stored original after raw row
          (canonicalEdges_member original row (same ▸ member)) path positive
        exact (List.mem_singleton.mp inside) ▸ found

private theorem head_positive {value result before after} (head : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (capDepth : Nat) (bounded : Cap Plain capDepth value) {path}
    (positive : PositiveAt result path) : PositiveAt value path := by
  cases head with
  | read fuel rows middle exposed built =>
    have phase := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
    have fields := EqualityLeafProjectionPhysical.makeNode_edges rows middle phase.2.1.ready.semantic.1.normal.facts.coherent phase.2.1.ready.semantic.1.normal.facts.linked phase.2.2.2
    have ordinary : Ordinary result := by simpa only [built] using SourceEqualityRequiredCache.node_ordinary rows middle phase.2.1.ready.semantic.1.normal.facts phase.2.2.2
    have raw : ∀ row ∈ nodeEdges result, row ∈ rows := by
      intro row member
      rw [built] at fields
      exact (List.mem_filter.mp (canonicalEdges_member _ row (fields ▸ member))).1
    cases positive with
    | root index row selected nonplain => exact read_positive (.done fuel exposed) semantic available guards capDepth bounded row (raw row (List.mem_of_getElem? selected)) [] nonplain
    | child index childIndex row child selected chosen rest => exact read_positive (.done fuel exposed) semantic available guards capDepth bounded row (raw row (List.mem_of_getElem? selected)) (childIndex :: _) ⟨child,chosen,rest⟩
    | member => cases ordinary

private theorem rows_guards {path index} {rows : List Row} {before values after} (actual : ProjectRows path index rows before values after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before rows) (guards : Guards before) : Guards after := by
  induction actual with
  | nil => exact guards
  | missing absent rest ih => exact ih semantic costs (fun row member => resident row (List.mem_cons_of_mem _ member)) guards
  | @selected row index child path before result middle rows values after chosen first rest ih =>
    have available := semantic.ready.semantic.1.normal.facts.cached.edges row.entry.key row (resident row List.mem_cons_self) child (select_member chosen)
    have phase := SourceEqualityProjectionCosts.project_effects first semantic costs available
    exact ih phase.2.1 phase.2.2.1 (fun row member => edge_grows before middle phase.1.growth row (resident row (List.mem_cons_of_mem _ member)))
      (SourceCurrentConstrainedCapProjectionGuard.node Plain first semantic costs available guards)

private theorem spine_positive {path value before result after} {project : Project path value before result after}
    {reader rows readAfter} {read : Read result reader rows readAfter} {position row}
    (spine : SourceCurrentProjectionReadSpine.Spine project read position row) :
    ∀ capDepth, SemanticReady before → CostHeap before → Available before value → Guards before →
    SemanticReady reader → CostHeap reader → Keeps after reader → Guards reader → Cap Plain capDepth value →
    ∀ residual, RowPositive row residual → PositiveAt value (path.map Int.toNat ++ residual) := by
  induction spine with
  | @root value state reader readAfter rows read position row selected =>
    intro capDepth semantic costs available guards readerSemantic readerCosts later readerGuards bounded residual positive
    exact read_positive read readerSemantic (later.available value available) readerGuards capDepth bounded row (List.mem_of_getElem? selected) residual positive
  | @ordinary path index sourceEdges before projectedMiddle values allRows unionMiddle result after
      entry depth free projects reads built reader rows readAfter read position row selected canonical rawIndex raw
      operandIndex operand operandSelected earlierRows selectedRows laterRows readStart readFinish
      readPrefix operandRead readSuffix parts readIndex readSelected sourceIndex sourceRow child start finish
      sourceSelected childSelected projectPrefix call projectSuffix rest ih =>
    intro capDepth semantic costs available guards readerSemantic readerCosts later readerGuards bounded residual positive
    have edges := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have earlierProject := SourceEqualityProjectionCosts.rows_effects projectPrefix semantic costs (fun row member => edges row (List.mem_of_mem_take member))
    have projected := SourceEqualityProjectionCosts.rows_effects projects semantic costs edges
    have earlier := SourceEqualityProjectionCosts.readAll_effects readPrefix projected.2.1 projected.2.2.1 (fun value member => projected.2.2.2 value (List.mem_of_mem_take member))
    have childAvailable := earlierProject.2.1.ready.semantic.1.normal.facts.cached.edges sourceRow.entry.key sourceRow
      (edge_grows before start earlierProject.1.growth sourceRow (edges sourceRow (List.mem_of_getElem? sourceSelected))) child (select_member childSelected)
    have called := SourceEqualityProjectionCosts.project_effects call earlierProject.2.1 earlierProject.2.2.1 childAvailable
    have suffix := SourceEqualityProjectionCosts.rows_effects projectSuffix called.2.1 called.2.2.1
      (fun row member => edge_grows before finish (grows_trans earlierProject.1.growth called.1.growth) row (edges row (List.mem_of_mem_drop member)))
    have childCap : Cap Plain (capDepth - 1) child := by
      have rowCap := SourceCurrentConstrainedCap.node_edge bounded sourceRow (List.mem_of_getElem? sourceSelected)
      cases capDepth with
      | zero => exact .plain 0 (rowCap.2 child (select_member childSelected))
      | succ capDepth => exact rowCap child (select_member childSelected)
    have firstGuards := rows_guards projectPrefix semantic costs (fun row member => edges row (List.mem_of_mem_take member)) guards
    have readGuards := SourceCurrentConstrainedCapProjectionGuard.readAll Plain readPrefix projected.2.1 projected.2.2.1
      (fun value member => projected.2.2.2 value (List.mem_of_mem_take member)) (rows_guards projects semantic costs edges guards)
    have childPositive := ih (capDepth - 1) earlierProject.2.1 earlierProject.2.2.1 childAvailable firstGuards earlier.2.1 earlier.2.2.1
      (suffix.1.trans earlier.1) readGuards childCap residual positive
    have chosen : sourceRow.children[index.toNat]? = some child := by
      unfold select at childSelected
      split at childSelected
      · cases childSelected
      · exact childSelected
    exact .child sourceIndex index.toNat sourceRow child sourceSelected chosen childPositive
  | @recursive original before exposed middle result after index path recursive head body reader rows readAfter read position row rest ih =>
    intro capDepth semantic costs available guards readerSemantic readerCosts later readerGuards bounded residual positive
    have phase := SourceEqualityProjectionCosts.head_effects head semantic costs available
    have cap := SourceCurrentConstrainedCapOpenExposure.head Plain capDepth head semantic costs available bounded (SourceCurrentConstrainedCapGuardNative.stored Plain before guards)
    exact head_positive head semantic costs available guards capDepth bounded (ih capDepth phase.2.1 phase.2.2.1 phase.2.2.2
      (SourceCurrentConstrainedCapProjectionGuard.head Plain head semantic costs available guards) readerSemantic readerCosts later readerGuards cap.2 residual positive)

/-- The same actual selected nonplain read row retains the full original natural path. -/
theorem root {path : List Nat} {value before result after} (project : Project (path.map Int.ofNat) value before result after)
    {reader rows readAfter} (read : Read result reader rows readAfter) (position : Nat) (row : Row) (selected : rows[position]? = some row)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) (guards : Guards before)
    (readerSemantic : SemanticReady reader) (readerCosts : CostHeap reader) (later : Keeps after reader) (readerGuards : Guards reader)
    (capDepth : Nat) (bounded : Cap Plain capDepth value) (nonplain : SourceMemoGate.plain row.entry.key.constraint = false) : PositiveAt value path := by
  have spine := SourceCurrentProjectionReadSpine.project project semantic costs available read position row selected
  simpa using spine_positive spine capDepth semantic costs available guards readerSemantic readerCosts later readerGuards bounded [] nonplain

/-- The same selected row and ordered child retain every positive descendant path. -/
theorem child {path residual : List Nat} {value before result after} (project : Project (path.map Int.ofNat) value before result after)
    {reader rows readAfter} (read : Read result reader rows readAfter) (position : Nat) (row : Row) (selected : rows[position]? = some row)
    (childIndex : Nat) (child : Node) (chosen : row.children[childIndex]? = some child) (positive : PositiveAt child residual)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) (guards : Guards before)
    (readerSemantic : SemanticReady reader) (readerCosts : CostHeap reader) (later : Keeps after reader) (readerGuards : Guards reader)
    (capDepth : Nat) (bounded : Cap Plain capDepth value) : PositiveAt value (path ++ childIndex :: residual) := by
  have spine := SourceCurrentProjectionReadSpine.project project semantic costs available read position row selected
  simpa using spine_positive spine capDepth semantic costs available guards readerSemantic readerCosts later readerGuards bounded (childIndex :: residual) ⟨child,chosen,positive⟩

end Actual
end MicroCFTA.SourceCurrentCappedProjectionPositivePosition
