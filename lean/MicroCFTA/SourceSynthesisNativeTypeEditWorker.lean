import MicroCFTA.SourceSynthesisNativeTypeSharedEdit
import MicroCFTA.SourceSynthesisNativeTypeSharedWorker
import MicroCFTA.SourceCurrentAllocatedSharedEditRanges
import MicroCFTA.SourceCurrentAllocatedSharedEditWorker
import MicroCFTA.SourceEqualityRequiredWorkerSound

/-!
# Type routes at actual executable current edit returns

Actual-prefix ranges supply the checks for reached native calls. Initial
structural routes prove each leaf input annotation. The ordered induction
derives each completed prefix graph before it enters the next range check.
No language inventory or completed edit graph is an input.

Successful worker returns and reached range checks remain explicit. These
laws do not prove completion, all reached source roles, failure-prefix
invariants, finite-word bounds, or native lazy demand order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeEditWorker
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityEdits (Edits)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
open SourceCurrentHereditaryTypeEditPlan
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes RowRoutes)
open SourceCurrentEditDomains (Populated HasLeaf)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditRanges
open SourceCurrentAllocatedSharedEditWorker (Outcome)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "worker" => SourceCurrentAllocatedSharedEditWorker.edit
local notation "childWorker" => SourceCurrentAllocatedSharedEditWorker.children
local notation "rowWorker" => SourceCurrentAllocatedSharedEditWorker.rows
local notation "listWorker" => SourceCurrentAllocatedSharedEditWorker.editList
variable {width : Nat}

private theorem bind_done {A B : Type} (first : Outcome width A)
    (next : A → SharedState width → Outcome width B) {result : B} {after : SharedState width}
    (done : first.bind next = .done result after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value middle => exact ⟨value, middle, rfl, done⟩
  | failed => cases done

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] in
private theorem work_done {A : Type} (request : Work Symbol Guard A) {before after : SharedState width}
    {result : A} (done : SourceCurrentAllocatedSharedEditWorker.work request before = .done result after) :
    ∃ heap, run request before.checked.native.machine.heap = (result, heap) ∧ after = advanceHeap before heap := by
  simp only [SourceCurrentAllocatedSharedEditWorker.work] at done
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj done
  exact ⟨_, rfl, rfl⟩

omit [DecidableEq Symbol] in
private theorem head_graph (fuel : Nat) {input result : Value Symbol Guard} {before after : SharedState width}
    (done : SourceCurrentAllocatedSharedEditWorker.head fuel input before = .done result after) :
    ∃ heap, SourceEqualityRequiredHead.Head input before.checked.native.machine.heap result heap ∧
      after = advanceHeap before heap := by
  cases actual : SourceEqualityRequiredWorker.head fuel input before.checked.native.machine.heap with
  | done value heap =>
      simp only [SourceCurrentAllocatedSharedEditWorker.head, actual] at done
      obtain ⟨rfl, rfl⟩ := Outcome.done.inj done
      exact ⟨heap, SourceEqualityRequiredWorkerSound.head_graph fuel _ _ _ _ actual, rfl⟩
  | pending | unresolved | exhausted =>
      simp only [SourceCurrentAllocatedSharedEditWorker.head, actual] at done
      cases done

private def NodeGraph (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (edits : Edits EqualityNormalize.Path)
    (input : Value Symbol Guard) (before : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated edits → HasLeaf edits → Available before.checked.native.machine.heap input → input.free = [] →
  NodePaths (Origin lib) edits input → ∀ e p h m s n output after,
  worker record originals e p h m s n edits input before = .done output after →
  EditNode record originals edits input before output after

private def ChildrenGraph (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (entries : List (Int × Edits EqualityNormalize.Path))
    (offset : Nat) (inputs : List (Value Symbol Guard)) (before : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated (.editBelow entries) → Values before.checked.native.machine.heap inputs → ClosedValues inputs →
  ChildrenPaths (Origin lib) entries offset inputs → ∀ e p h m s n outputs after,
  childWorker (worker record originals e p h m s n) entries offset inputs before = .done outputs after →
  EditChildren record originals entries offset inputs before outputs after

private def RowsGraph (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (entries : List (Int × Edits EqualityNormalize.Path))
    (inputs : List (EdgeValue Symbol Guard)) (before : SharedState width) : Prop :=
  Ready lib before → Values before.checked.native.machine.heap originals → ClosedValues originals →
  (∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals) →
  Populated (.editBelow entries) → Edges before.checked.native.machine.heap inputs → ClosedEdges inputs →
  (∀ row ∈ inputs, ChildrenPaths (Origin lib) entries 0 row.children) → ∀ e p h m s n outputs after,
  rowWorker (worker record originals e p h m s n) entries inputs before = .done outputs after →
  EditRows record originals entries inputs before outputs after

private theorem graphs (lib : Library) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) :
    (∀ edits input before, NodeRanges (width := width) record originals edits input before →
      NodeGraph lib record originals edits input before) ∧
    (∀ entries offset inputs before, ChildrenRanges (width := width) record originals entries offset inputs before →
      ChildrenGraph lib record originals entries offset inputs before) ∧
    (∀ entries inputs before, RowsRanges (width := width) record originals entries inputs before →
      RowsGraph lib record originals entries inputs before) := by
  have leafCase : ∀ {target input before},
      SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals target input before →
      NodeGraph (width := width) lib record originals (.editAt target) input before := by
    intro target input before ranges ready originalAvailable originalClosed originalRoutes _ _ available closed paths
      e p h m s n output after done
    cases e with
    | zero => cases done
    | succ e =>
        change SourceCurrentAllocatedSharedEditWorker.leaf p h m s n record originals target input before = .done output after at done
        cases actual : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals target input before with
        | failed =>
            simp only [SourceCurrentAllocatedSharedEditWorker.leaf, SourceCurrentAllocatedSharedEditWorker.lift, actual] at done
            cases done
        | done value final =>
            simp only [SourceCurrentAllocatedSharedEditWorker.leaf, SourceCurrentAllocatedSharedEditWorker.lift, actual] at done
            obtain ⟨rfl, rfl⟩ := Outcome.done.inj done
            exact .leaf (SourceSynthesisNativeTypeSharedWorker.leaf lib p h m s n ready originalAvailable
              originalClosed originalRoutes available closed (leaf_annotated paths) ranges actual).1
  have emptyCase : ∀ {entries before},
      NodeGraph (width := width) lib record originals (.editBelow entries) (.empty : Value Symbol Guard) before := by
    intro entries before _ _ _ _ _ _ _ _ _ e p h m s n output after done
    cases e with
    | zero => cases done
    | succ e => cases done; exact .empty
  have ordinaryCase : ∀ {entries edges before entry depth free},
      RowsRanges record originals entries edges before →
      RowsGraph (width := width) lib record originals entries edges before →
      NodeGraph (width := width) lib record originals (.editBelow entries) (.node entry edges depth free) before := by
    intro entries edges before entry depth free _ ih ready originalAvailable originalClosed originalRoutes populated _ available closed paths
      e p h m s n output after done
    cases e with
    | zero => cases done
    | succ e =>
        change (rowWorker (worker record originals e p h m s n) entries edges before).bind
          (fun rebuilt middle => SourceCurrentAllocatedSharedEditWorker.work (makeNode rebuilt) middle) = .done output after at done
        obtain ⟨rebuilt, middle, rowsDone, built⟩ := bind_done _ _ done
        have facts := ready.checked.semantic.ready.semantic.1.normal.facts
        have lower := ih ready originalAvailable originalClosed originalRoutes populated
          (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
          (MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed)
          (fun row member => node_to_children paths row member) e p h m s n rebuilt middle rowsDone
        obtain ⟨heap, made, rfl⟩ := work_done (makeNode rebuilt) built
        exact .ordinary lower made
  have recursiveCase : ∀ {input entries} {before : SharedState width},
      SourceEqualityRequiredGraph.Recursive input →
      (∀ exposed heap, SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap →
        NodeRanges record originals (.editBelow entries) exposed (advanceHeap before heap)) →
      (∀ exposed heap, SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap →
        NodeGraph (width := width) lib record originals (.editBelow entries) exposed (advanceHeap before heap)) →
      NodeGraph (width := width) lib record originals (.editBelow entries) input before := by
    intro input entries before recursive _ ih ready originalAvailable originalClosed originalRoutes populated nonempty available closed paths
      e p h m s n output after done
    cases e with
    | zero => cases done
    | succ e =>
        have unfolded : (SourceCurrentAllocatedSharedEditWorker.head h input before).bind
            (fun exposed middle => worker record originals e p h m s n (.editBelow entries) exposed middle) = .done output after := by
          cases input <;> cases recursive <;> exact done
        obtain ⟨exposed, middle, read, returned⟩ := bind_done _ _ unfolded
        obtain ⟨heap, head, rfl⟩ := head_graph h read
        obtain ⟨current, first, exposedAvailable, exposedClosed, exposedTyped⟩ :=
          SourceSynthesisNativeTypeSharedHeap.head lib head ready available closed
            (recursive_annotated recursive nonempty paths)
        have body := ih exposed heap head current
          (fun original member => first.available original (originalAvailable original member)) originalClosed originalRoutes
          populated nonempty exposedAvailable exposedClosed (fun path _ _ => .annotated path exposed exposedTyped)
          e p h m s n output after returned
        exact .recursive recursive head body
  have nilChildren : ∀ {entries offset before},
      ChildrenGraph (width := width) lib record originals entries offset ([] : List (Value Symbol Guard)) before := by
    intro entries offset before _ _ _ _ _ _ _ _ e p h m s n outputs after done
    cases done
    exact .nil
  have unselectedCase : ∀ {entries inputs before input} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      ChildrenRanges record originals entries (offset + 1) inputs before →
      ChildrenGraph (width := width) lib record originals entries (offset + 1) inputs before →
      ChildrenGraph (width := width) lib record originals entries offset (input :: inputs) before := by
    intro entries inputs before input offset absent _ ih ready originalAvailable originalClosed originalRoutes populated available closed paths
      e p h m s n outputs after done
    simp only [SourceCurrentAllocatedSharedEditWorker.children, absent] at done
    obtain ⟨results, final, returned, finished⟩ := bind_done _ _ done
    obtain ⟨rfl, rfl⟩ := Outcome.done.inj finished
    exact .unselected offset absent (ih ready originalAvailable originalClosed originalRoutes populated
      (fun value member => available value (List.mem_cons_of_mem _ member))
      (fun value member => closed value (List.mem_cons_of_mem _ member)) (children_tail paths)
      e p h m s n results final returned)
  have selectedCase : ∀ {entries edits input before inputs} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      NodeRanges record originals edits input before →
      (∀ result middle, EditNode record originals edits input before result middle →
        ChildrenRanges record originals entries (offset + 1) inputs middle) →
      NodeGraph (width := width) lib record originals edits input before →
      (∀ result middle, EditNode record originals edits input before result middle →
        ChildrenGraph (width := width) lib record originals entries (offset + 1) inputs middle) →
      ChildrenGraph (width := width) lib record originals entries offset (input :: inputs) before := by
    intro entries edits input before inputs offset found _ _ firstIH restIH ready originalAvailable originalClosed originalRoutes
      populated available closed paths e p h m s n outputs after done
    simp only [SourceCurrentAllocatedSharedEditWorker.children, found] at done
    obtain ⟨result, middle, firstDone, later⟩ := bind_done _ _ done
    obtain ⟨results, final, restDone, finished⟩ := bind_done _ _ later
    obtain ⟨rfl, rfl⟩ := Outcome.done.inj finished
    have childPopulated := selected_populated populated found
    have childPaths := children_selected paths found
    have firstGraph := firstIH ready originalAvailable originalClosed originalRoutes childPopulated.1 childPopulated.2
      (available input List.mem_cons_self) (closed input List.mem_cons_self) childPaths e p h m s n result middle firstDone
    obtain ⟨current, first, _, _, _⟩ := SourceSynthesisNativeTypeSharedEdit.node lib firstGraph ready
      originalAvailable originalClosed originalRoutes childPopulated.1 childPopulated.2
      (available input List.mem_cons_self) (closed input List.mem_cons_self) childPaths
    have restGraph := restIH result middle firstGraph current
      (fun original member => first.available original (originalAvailable original member)) originalClosed originalRoutes populated
      (fun value member => first.available value (available value (List.mem_cons_of_mem _ member)))
      (fun value member => closed value (List.mem_cons_of_mem _ member)) (children_tail paths)
      e p h m s n results final restDone
    exact .selected offset found firstGraph restGraph
  have nilRows : ∀ {entries before},
      RowsGraph (width := width) lib record originals entries ([] : List (EdgeValue Symbol Guard)) before := by
    intro entries before _ _ _ _ _ _ _ _ e p h m s n outputs after done
    cases done
    exact .nil
  have consRows : ∀ {entries edges before} {edge : EdgeValue Symbol Guard},
      ChildrenRanges record originals entries 0 edge.children before →
      (∀ values middle, EditChildren record originals entries 0 edge.children before values middle →
        RowsRanges record originals entries edges (advanceHeap middle
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2)) →
      ChildrenGraph (width := width) lib record originals entries 0 edge.children before →
      (∀ values middle, EditChildren record originals entries 0 edge.children before values middle →
        RowsGraph (width := width) lib record originals entries edges (advanceHeap middle
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2)) →
      RowsGraph (width := width) lib record originals entries (edge :: edges) before := by
    intro entries edges before edge _ _ firstIH restIH ready originalAvailable originalClosed originalRoutes populated resident closed paths
      e p h m s n outputs after done
    change (childWorker (worker record originals e p h m s n) entries 0 edge.children before).bind
      (fun values middle => (SourceCurrentAllocatedSharedEditWorker.work
        (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
        (rowWorker (worker record originals e p h m s n) entries edges afterEdge).bind
          fun results final => .done (result :: results) final) = .done outputs after at done
    obtain ⟨values, middle, childrenDone, later⟩ := bind_done _ _ done
    obtain ⟨result, afterEdge, edgeDone, remaining⟩ := bind_done _ _ later
    obtain ⟨results, final, restDone, finished⟩ := bind_done _ _ remaining
    obtain ⟨rfl, rfl⟩ := Outcome.done.inj finished
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have edgeAvailable := facts.cached.edges _ _ (resident edge List.mem_cons_self)
    have edgeClosed := closed edge List.mem_cons_self
    have edgePaths := paths edge List.mem_cons_self
    have childGraph := firstIH ready originalAvailable originalClosed originalRoutes populated edgeAvailable edgeClosed edgePaths
      e p h m s n values middle childrenDone
    obtain ⟨current, first, valuesAvailable, _, _⟩ := SourceSynthesisNativeTypeSharedEdit.children lib childGraph ready
      originalAvailable originalClosed originalRoutes populated edgeAvailable edgeClosed edgePaths
    obtain ⟨heap, made, rfl⟩ := work_done _ edgeDone
    have oldRow := InternedEdgeResidency.edge_grows _ _ first.heap edge (resident edge List.mem_cons_self)
    obtain ⟨constructed, second, _, _, _⟩ :=
      SourceSynthesisNativeTypeSharedHeap.edge lib edge values made current oldRow valuesAvailable
    have preceding := first.trans second
    have follow := restIH values middle childGraph
    simp only [made] at follow
    have restGraph := follow constructed
      (fun original member => preceding.available original (originalAvailable original member)) originalClosed originalRoutes populated
      (fun row member => InternedEdgeResidency.edge_grows _ _ preceding.heap row (resident row (List.mem_cons_of_mem _ member)))
      (fun row member => closed row (List.mem_cons_of_mem _ member))
      (fun row member => paths row (List.mem_cons_of_mem _ member)) e p h m s n results final restDone
    exact .cons childGraph made restGraph
  refine ⟨?_, ?_, ?_⟩
  · intro edits input before ranges
    exact NodeRanges.rec
      (motive_1 := fun edits input before _ => NodeGraph lib record originals edits input before)
      (motive_2 := fun entries offset inputs before _ => ChildrenGraph lib record originals entries offset inputs before)
      (motive_3 := fun entries inputs before _ => RowsGraph lib record originals entries inputs before)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consRows ranges
  · intro entries offset inputs before ranges
    exact ChildrenRanges.rec
      (motive_1 := fun edits input before _ => NodeGraph lib record originals edits input before)
      (motive_2 := fun entries offset inputs before _ => ChildrenGraph lib record originals entries offset inputs before)
      (motive_3 := fun entries inputs before _ => RowsGraph lib record originals entries inputs before)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consRows ranges
  · intro entries inputs before ranges
    exact RowsRanges.rec
      (motive_1 := fun edits input before _ => NodeGraph lib record originals edits input before)
      (motive_2 := fun entries offset inputs before _ => ChildrenGraph lib record originals entries offset inputs before)
      (motive_3 := fun entries inputs before _ => RowsGraph lib record originals entries inputs before)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consRows ranges

/-- A literal current node return derives its graph and all Type facts from initial routes. -/
theorem node (lib : Library) (e p h m s n : Nat) {record originals edits input output} {before after : SharedState width}
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated edits) (nonempty : HasLeaf edits)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (paths : NodePaths (Origin lib) edits input) (ranges : NodeRanges record originals edits input before)
    (done : worker record originals e p h m s n edits input before = .done output after) :
    EditNode record originals edits input before output after ∧ Ready lib after ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap output ∧ output.free = [] ∧
      ∀ path, TypePath (Origin lib) path input → TypePath (Origin lib) path output := by
  have actual := (graphs lib record originals).1 _ _ _ ranges ready originalAvailable originalClosed originalRoutes
    populated nonempty available closed paths e p h m s n output after done
  exact ⟨actual, SourceSynthesisNativeTypeSharedEdit.node lib actual ready originalAvailable originalClosed originalRoutes
    populated nonempty available closed paths⟩

/-- A literal current child scan derives each actual prefix before its later range check. -/
theorem children (lib : Library) (e p h m s n : Nat) {record originals entries offset inputs outputs} {before after : SharedState width}
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (available : Values before.checked.native.machine.heap inputs)
    (closed : ClosedValues inputs) (paths : ChildrenPaths (Origin lib) entries offset inputs)
    (ranges : ChildrenRanges record originals entries offset inputs before)
    (done : childWorker (worker record originals e p h m s n) entries offset inputs before = .done outputs after) :
    EditChildren record originals entries offset inputs before outputs after ∧ Ready lib after ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Values after.checked.native.machine.heap outputs ∧ ClosedValues outputs ∧ ForestRoutes (Origin lib) inputs outputs := by
  have actual := (graphs lib record originals).2.1 _ _ _ _ ranges ready originalAvailable originalClosed originalRoutes
    populated available closed paths e p h m s n outputs after done
  exact ⟨actual, SourceSynthesisNativeTypeSharedEdit.children lib actual ready originalAvailable originalClosed originalRoutes
    populated available closed paths⟩

/-- Actual full-guard row rebuilding derives its graph and preserves every child route. -/
theorem rows (lib : Library) (e p h m s n : Nat) {record originals entries inputs outputs} {before after : SharedState width}
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (resident : Edges before.checked.native.machine.heap inputs)
    (closed : ClosedEdges inputs) (paths : ∀ row ∈ inputs, ChildrenPaths (Origin lib) entries 0 row.children)
    (ranges : RowsRanges record originals entries inputs before)
    (done : rowWorker (worker record originals e p h m s n) entries inputs before = .done outputs after) :
    EditRows record originals entries inputs before outputs after ∧ Ready lib after ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Edges after.checked.native.machine.heap outputs ∧ ClosedEdges outputs ∧ RowRoutes (Origin lib) inputs outputs := by
  have actual := (graphs lib record originals).2.2 _ _ _ ranges ready originalAvailable originalClosed originalRoutes
    populated resident closed paths e p h m s n outputs after done
  exact ⟨actual, SourceSynthesisNativeTypeSharedEdit.rows lib actual ready originalAvailable originalClosed originalRoutes
    populated resident closed paths⟩

/-- Actual executable list returns use Type-only initial facts and reached range checks. -/
theorem list (lib : Library) (e p h m s n : Nat) {record originals edits inputs outputs} {before after : SharedState width}
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated edits) (available : Values before.checked.native.machine.heap inputs)
    (closed : ClosedValues inputs) (paths : ForestPaths (Origin lib) edits inputs)
    (ranges : ListRanges record originals edits inputs before)
    (done : listWorker (worker record originals e p h m s n) edits inputs before = .done outputs after) :
    EditList record originals edits inputs before outputs after ∧ Ready lib after ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Values after.checked.native.machine.heap outputs ∧ ClosedValues outputs ∧ ForestRoutes (Origin lib) inputs outputs := by
  have actual : EditList record originals edits inputs before outputs after := by
    cases edits with
    | editAt target => cases done; exact .leaf
    | editBelow entries =>
        exact .children ((graphs lib record originals).2.1 entries 0 inputs before ranges ready originalAvailable originalClosed
          originalRoutes populated available closed (forest_to_children paths) e p h m s n outputs after done)
  exact ⟨actual, SourceSynthesisNativeTypeSharedEdit.list lib actual ready originalAvailable originalClosed originalRoutes
    populated available closed paths⟩

end MicroCFTA.SourceSynthesisNativeTypeEditWorker
