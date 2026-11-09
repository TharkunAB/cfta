import MicroCFTA.SourceEqualityRequiredExecution

/-!
# Physical shapes at strict required-path prefixes

A terminal Needed map does not inspect its value. A nonempty map returns
Empty or an ordinary node. Each selected nonnegative child position retains
the corresponding property recursively. Negative map keys keep their source
lookup behavior. No shape is imposed at an unconstrained terminal endpoint.
-/
namespace MicroCFTA.SourceEqualityRequiredPathShape
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident edge_grows)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredGraph
variable {Symbol Guard : Type}

/-- Actual required prefixes are ordinary; terminal endpoints can have any shape. -/
inductive PrefixShape : Needed → Value Symbol Guard → Prop where
  | terminal (value : Value Symbol Guard) : PrefixShape (.node []) value
  | empty (entries : List (Int × Needed)) : PrefixShape (.node entries) .empty
  | node (entries : List (Int × Needed)) (entry : Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
      (children : ∀ edge ∈ rows, ∀ (index : Nat) value needed,
        edge.children[index]? = some value →
        SourceEqualityNeededMap.lookup (index : Int) entries = some needed → PrefixShape needed value) :
      PrefixShape (.node entries) (.node entry rows depth free)

/-- Ordered children use the literal offset and signed map lookup of the worker. -/
def ChildrenShape (entries : List (Int × Needed)) (offset : Nat)
    (values : List (Value Symbol Guard)) : Prop :=
  ∀ index value needed, values[index]? = some value →
    SourceEqualityNeededMap.lookup ((offset + index : Nat) : Int) entries = some needed →
      PrefixShape needed value

/-- Every surviving physical row has the required shapes at its actual child positions. -/
def RowsShape (entries : List (Int × Needed)) (rows : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ rows, ChildrenShape entries 0 edge.children

/-- A nonempty required map cannot return an opaque record. -/
theorem PrefixShape.ordinary {entries : List (Int × Needed)} {value : Value Symbol Guard}
    (shape : PrefixShape (.node entries) value) (nonempty : entries ≠ []) :
    SourceEqualityRequiredCache.Ordinary value := by
  cases shape with
  | terminal => exact (nonempty rfl).elim
  | empty | node => trivial

/-- A selected ordinary child retains the exact subtree from the signed required map. -/
theorem PrefixShape.child {entries : List (Int × Needed)}
    {entry : Interned InternedBinderProtocol.NodeKey} {rows : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference}
    (shape : PrefixShape (.node entries) (.node entry rows depth free))
    {edge : EdgeValue Symbol Guard} (member : edge ∈ rows)
    {index : Nat} {value : Value Symbol Guard} {needed : Needed}
    (found : edge.children[index]? = some value)
    (selected : SourceEqualityNeededMap.lookup (index : Int) entries = some needed) :
    PrefixShape needed value := by
  cases shape with
  | terminal => cases selected
  | node _ _ _ _ _ children => exact children edge member index value needed found selected

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem children_verified
    {entries : List (Int × Needed)} {offset : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard}
    (actual : RequireChildren entries offset values before results after)
    (ready : Ready before) (available : Values before values) (closed : ClosedValues values) :
    Keeps before after ∧ Values after results ∧ ClosedValues results := by
  have callbacks : SourceEqualityRequiredListsComplete.ChildComplete (Symbol := Symbol) (Guard := Guard) entries :=
    fun _ needed _ value current ready available closed =>
      SourceEqualityRequiredComplete.complete needed value current ready available closed
  obtain ⟨canonical, reached, trace, kept, resident, resultClosed⟩ :=
    SourceEqualityRequiredListsComplete.children_complete entries callbacks offset values before ready available closed
  obtain ⟨sameValue, sameState⟩ := SourceEqualityRequiredExecution.children_unique trace actual
  cases sameValue
  cases sameState
  exact ⟨kept, resident, resultClosed⟩

private theorem rows_verified
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireRows entries edges before results after)
    (ready : Ready before) (resident : Edges before edges) (closed : ClosedEdges edges) :
    Keeps before after ∧ Edges after results ∧ ClosedEdges results := by
  have callbacks : SourceEqualityRequiredListsComplete.ChildComplete (Symbol := Symbol) (Guard := Guard) entries :=
    fun _ needed _ value current ready available closed =>
      SourceEqualityRequiredComplete.complete needed value current ready available closed
  obtain ⟨canonical, reached, trace, kept, resultResident, resultClosed⟩ :=
    SourceEqualityRequiredListsComplete.rows_complete entries callbacks edges before ready resident closed
  obtain ⟨sameValue, sameState⟩ := SourceEqualityRequiredExecution.stable_unique
    (SourceEqualityRequiredWorkerComplete.rows_stable trace)
    (SourceEqualityRequiredWorkerComplete.rows_stable actual)
  cases sameValue
  cases sameState
  exact ⟨kept, resultResident, resultClosed⟩

private theorem makeNode_shape (entries : List (Int × Needed))
    (rows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (facts : Facts before) (resident : Edges before rows) (shape : RowsShape entries rows) :
    PrefixShape (.node entries) (run (makeNode rows) before).1 := by
  have selected : Edges before (canonicalEdges (surviving rows)) :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedShape : RowsShape entries (canonicalEdges (surviving rows)) :=
    fun edge member => shape edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact .empty entries
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := InternedEdgeResidency.identifyNode_readback (first :: rest) before facts.coherent facts.linked
      (by simpa [InternedNestedProvenance.Edges, same] using selected)
    simp only [run, readback, identifyNode]
    apply PrefixShape.node
    intro edge member index value needed found lookup
    have row := selectedShape edge (by simpa only [same] using member)
    exact row index value needed found (by simpa only [Nat.zero_add] using lookup)

private def NodeProperty (needed : Needed) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) : Prop :=
  Ready before → Available before value → value.free = [] → PrefixShape needed result

private def ChildrenProperty (entries : List (Int × Needed)) (offset : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) : Prop :=
  Ready before → Values before values → ClosedValues values → ChildrenShape entries offset results

private def RowsProperty (entries : List (Int × Needed)) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) : Prop :=
  Ready before → Edges before edges → ClosedEdges edges → RowsShape entries results

private theorem shapes :
    (∀ needed (value : Value Symbol Guard) before result after,
      RequireNode needed value before result after → NodeProperty needed value before result) ∧
    (∀ entries offset (values : List (Value Symbol Guard)) before results after,
      RequireChildren entries offset values before results after →
        ChildrenProperty entries offset values before results) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      RequireRows entries edges before results after → RowsProperty entries edges before results) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodeProperty (.node []) value state value := by
    intro value state _ _ _
    exact .terminal value
  have emptyCase : ∀ {entries : List (Int × Needed)} {state},
      entries ≠ [] → NodeProperty (.node entries) (.empty : Value Symbol Guard) state .empty := by
    intro entries state _ _ _ _
    exact .empty entries
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (result, after) → RowsProperty entries edges before rebuilt →
      NodeProperty (.node entries) (.node entry edges depth free) before result := by
    intro entries edges before rebuilt middle result after entry depth free _ rows actual ih ready available closed
    have facts := ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have edgeClosed := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
    have info := rows_verified rows ready resident edgeClosed
    have shape := makeNode_shape entries rebuilt middle info.1.ready.semantic.1.normal.facts info.2.1
      (ih ready resident edgeClosed)
    simpa only [actual] using shape
  have recursiveCase : ∀ {entries original before exposed middle result after},
      entries ≠ [] → Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after →
      NodeProperty (.node entries) exposed middle result → NodeProperty (.node entries) original before result := by
    intro entries original before exposed middle result after _ _ head _ ih ready available closed
    have info := head.verified ready available closed
    exact ih info.1.ready info.2.1 info.2.2.1
  have nilChildren : ∀ {entries : List (Int × Needed)} {offset : Nat} {state},
      ChildrenProperty (Symbol := Symbol) (Guard := Guard) entries offset [] state [] := by
    intro entries offset state _ _ _ index value needed found _
    cases index <;> cases found
  have unselectedCase : ∀ {entries values before results after value} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (offset + 1) values before results after →
      ChildrenProperty entries (offset + 1) values before results →
      ChildrenProperty entries offset (value :: values) before (value :: results) := by
    intro entries values before results after value offset absent _ ih ready available closed
    have tail := ih ready
      (fun child member => available child (List.mem_cons_of_mem _ member))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    intro index child needed found selected
    cases index with
    | zero =>
        simp only [Nat.add_zero, absent] at selected
        cases selected
    | succ index =>
        have shifted : offset + (index + 1) = (offset + 1) + index := by omega
        exact tail index child needed found (by simpa only [← shifted] using selected)
  have selectedCase : ∀ {entries needed value before result middle values results after} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (offset + 1) values middle results after →
      NodeProperty needed value before result → ChildrenProperty entries (offset + 1) values middle results →
      ChildrenProperty entries offset (value :: values) before (result :: results) := by
    intro entries needed value before result middle values results after offset lookup first _ ownIH tailIH ready available closed
    have info := SourceEqualityRequiredExecution.node_verified first ready
      (available value List.mem_cons_self) (closed value List.mem_cons_self)
    have own := ownIH ready (available value List.mem_cons_self) (closed value List.mem_cons_self)
    have tail := tailIH info.1.ready
      (fun child member => info.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    intro index child selectedNeeded found selected
    cases index with
    | zero =>
        cases Option.some.inj found
        simp only [Nat.add_zero] at selected
        have same := Option.some.inj (lookup.symm.trans selected)
        exact same ▸ own
    | succ index =>
        have shifted : offset + (index + 1) = (offset + 1) + index := by omega
        exact tail index child selectedNeeded found (by simpa only [← shifted] using selected)
  have nilRows : ∀ {entries : List (Int × Needed)} {state},
      RowsProperty (Symbol := Symbol) (Guard := Guard) entries [] state [] := by
    intro entries state _ _ _ edge member
    cases member
  have rejectedCase : ∀ {entries edges before results after edge},
      fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after →
      RowsProperty entries edges before results → RowsProperty entries (edge :: edges) before results := by
    intro entries edges before results after edge _ _ ih ready resident closed
    exact ih ready
      (fun row member => resident row (List.mem_cons_of_mem _ member))
      (fun row member => closed row (List.mem_cons_of_mem _ member))
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ChildrenProperty entries 0 edge.children before values → RowsProperty entries edges afterEdge results →
      RowsProperty entries (edge :: edges) before (result :: results) := by
    intro entries before values middle result afterEdge edges results after edge _ children rebuilt _ childIH restIH ready resident closed
    have available := ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have childInfo := children_verified children ready available (closed edge List.mem_cons_self)
    have own := childIH ready available (closed edge List.mem_cons_self)
    have built := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values
      middle childInfo.1.ready childInfo.2.1
    have edgeKeeps : Keeps middle afterEdge := by simpa only [rebuilt] using built.1
    have childrenSame : result.children = values := by simpa only [rebuilt] using built.2.2
    have combined := childInfo.1.trans edgeKeeps
    have tail := restIH edgeKeeps.ready
      (fun row member => edge_grows before afterEdge combined.growth row (resident row (List.mem_cons_of_mem _ member)))
      (fun row member => closed row (List.mem_cons_of_mem _ member))
    intro row member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [childrenSame] using own
    · exact tail row member
  constructor
  · intro needed value before result after trace
    exact RequireNode.rec
      (motive_1 := fun needed value before result _ _ => NodeProperty needed value before result)
      (motive_2 := fun entries offset values before results _ _ => ChildrenProperty entries offset values before results)
      (motive_3 := fun entries edges before results _ _ => RowsProperty entries edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  constructor
  · intro entries offset values before results after trace
    exact RequireChildren.rec
      (motive_1 := fun needed value before result _ _ => NodeProperty needed value before result)
      (motive_2 := fun entries offset values before results _ _ => ChildrenProperty entries offset values before results)
      (motive_3 := fun entries edges before results _ _ => RowsProperty entries edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries edges before results after trace
    exact RequireRows.rec
      (motive_1 := fun needed value before result _ _ => NodeProperty needed value before result)
      (motive_2 := fun entries offset values before results _ _ => ChildrenProperty entries offset values before results)
      (motive_3 := fun entries edges before results _ _ => RowsProperty entries edges before results)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace

/-- A successful physical node graph derives ordinary exposure at every strict required prefix. -/
theorem node_shape {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (ready : Ready before)
    (available : Available before value) (closed : value.free = []) : PrefixShape needed result :=
  shapes.1 _ _ _ _ _ actual ready available closed

/-- The actual child graph derives recursive shapes at its literal positive-index lookups. -/
theorem children_shape {entries : List (Int × Needed)} {offset : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries offset values before results after) (ready : Ready before)
    (available : Values before values) (closed : ClosedValues values) : ChildrenShape entries offset results :=
  shapes.2.1 _ _ _ _ _ _ actual ready available closed

/-- Row rejection and actual edge reconstruction retain every surviving required prefix. -/
theorem rows_shape {entries : List (Int × Needed)} {rows results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireRows entries rows before results after)
    (ready : Ready before) (resident : Edges before rows) (closed : ClosedEdges rows) : RowsShape entries results :=
  shapes.2.2 _ _ _ _ _ actual ready resident closed

/-- Literal successful require execution derives the same prefix certificate. -/
theorem require_shape {fuel readFuel : Nat} {needed : Needed} {value result : Value Symbol Guard}
    {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredWorker.require fuel readFuel needed value before = .done result after)
    (ready : Ready before) (available : Available before value) (closed : value.free = []) :
    PrefixShape needed result :=
  node_shape (SourceEqualityRequiredWorkerSound.require_graph fuel readFuel needed value before result after actual)
    ready available closed

/-- Actual requireAll success derives strict-prefix shapes from the source-compiled Needed map. -/
theorem requireAll_shape {fuel readFuel : Nat} {paths : List Path}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (ready : Ready before) (available : Values before values) (closed : ClosedValues values) :
    match build paths with | .node entries => ChildrenShape entries 0 results := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, actual⟩
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at graph
      exact children_shape graph ready available closed
end MicroCFTA.SourceEqualityRequiredPathShape
