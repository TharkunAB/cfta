import MicroCFTA.SourceMergedAnnotationSelection
import MicroCFTA.SourceMergedSoundness

/-!
# Physical annotation heaps through actual general source merging

The proof retains the actual comparison filter, recursive boundary test,
four-row threshold, original small-row guards, and large-row Top guard.
Existing source effects derive each intermediate scope. Annotation effects
follow the same requests and do not assume a complete output invariant.
-/
namespace MicroCFTA.SourceMergedAnnotationWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (Effect bind_done)
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure bind work map retainedColumn small)
open SourceMergedContracts
open SourceEqualityAnnotationHeap (Heap)

/-- Recursive annotation preservation is required only at actual successful closed calls. -/
def RecurseHeap (annotation : Guard → Prop) (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before, SemanticReady before → Available before value → value.free = [] →
    ∀ result after, call value before = .done result after → Heap annotation before → Heap annotation after

/-- Ordered maps retain annotations through the actual effects of each earlier request. -/
theorem map_heap (annotation : Guard → Prop) (call : Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (requests : List Request)
    (effects : ∀ request ∈ requests, ∀ before, SemanticReady before → pre before request →
      ∀ result after, call request before = .done result after → Effect before after)
    (annotations : ∀ request ∈ requests, ∀ before, SemanticReady before → pre before request →
      ∀ result after, call request before = .done result after → Heap annotation before → Heap annotation after)
    (before : State Symbol Guard) (semantic : SemanticReady before) (inputs : ∀ request ∈ requests, pre before request)
    (results : List Output) (after : State Symbol Guard) (done : map call requests before = .done results after)
    (heap : Heap annotation before) : Heap annotation after := by
  induction requests generalizing before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact heap
  | cons request requests ih =>
      obtain ⟨first, middle, called, later⟩ := (bind_done _ _ results after).mp done
      have checked := effects request List.mem_cons_self before semantic (inputs request List.mem_cons_self) first middle called
      have middleHeap := annotations request List.mem_cons_self before semantic (inputs request List.mem_cons_self) first middle called heap
      obtain ⟨rest, final, mapped, returned⟩ := (bind_done _ _ results after).mp later
      have finalHeap := ih (fun request member => effects request (List.mem_cons_of_mem _ member))
        (fun request member => annotations request (List.mem_cons_of_mem _ member)) middle checked.2
        (fun request member => preGrows before middle checked request (inputs request (List.mem_cons_of_mem _ member))) rest final mapped middleHeap
      have parts := Result.done.inj returned
      cases parts.2
      exact finalHeap

/-- Every retained-column branch preserves annotations through literal union work and actual recursion. -/
theorem retained_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (annotations : RecurseHeap annotation call)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn call inputs before = .done result after) (heap : Heap annotation before) : Heap annotation after := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values)
      (done : (if values.any MergedOrdinaryHeight.recursiveBoundary then work (makeUnion values)
        else bind (work (MergedOrdinaryHeight.ordinaryUnion values)) call) before = .done result after) : Heap annotation after := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true, work] at done
      have parts := Result.done.inj done
      cases parts.2
      exact SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeUnion annotation values) before heap
    · simp only [boundary, Bool.false_eq_true, ite_false] at done
      obtain ⟨united, middle, constructed, called⟩ := (bind_done _ _ result after).mp done
      have parts := Result.done.inj constructed
      cases parts.1; cases parts.2
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      exact annotations _ _ checked.1.2 checked.2.1 checked.2.2.1 result after called
        (SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeNode annotation _) before heap)
  cases inputs with
  | nil => exact branches [] available closed done
  | cons first rest =>
      cases rest with
      | nil =>
          have parts := Result.done.inj done
          cases parts.2
          exact heap
      | cons second rest => exact branches (first :: second :: rest) available closed done

/-- The actual repaired child filter and retained-column requests preserve annotations in order. -/
theorem column_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (annotations : RecurseHeap annotation call)
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before inputs) (closed : ClosedValues inputs)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.column call clear fuel inputs before = .done result after) (heap : Heap annotation before) : Heap annotation after := by
  obtain ⟨selected, middle, filtered, called⟩ := (bind_done _ _ result after).mp done
  have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
    (fun _ _ _ => rfl) inputs before semantic available closed selected middle filtered
  have filteredHeap := (SourceMergedAnnotationSelection.select_effect annotation clear fuel inputs before semantic available closed selected middle filtered).annotations heap
  exact retained_heap annotation call annotations selected middle checked.1.2 checked.2.1 checked.2.2.1 result after called filteredHeap

/-- Small rows retain their actual original full guard after ordered recursive child effects. -/
theorem small_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (annotations : RecurseHeap annotation call)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : EdgeResident before edge) (closed : ClosedValues edge.children) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) (heap : Heap annotation before) : Heap annotation after := by
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  have middleHeap := map_heap annotation call (fun state value => Available state value ∧ value.free = [])
    (fun _ _ effect value valid => ⟨effect.1.available value valid.1, valid.2⟩) edge.children
    (fun value _ state ready valid result final actual => (law value state ready valid.1 valid.2 result final actual).1)
    (fun value _ state ready valid result final actual => annotations value state ready valid.1 valid.2 result final actual)
    before semantic (fun value member => ⟨available value member, closed value member⟩) values middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact SourceEqualityAnnotationHeap.run annotation _
    (SourceEqualityAnnotationHeap.makeEdge annotation edge.entry.key.symbol edge.entry.key.constraint values (heap edge.entry.key edge resident)) middle middleHeap

/-- Large groups retain annotations through actual columns and the literal source Top guard. -/
theorem large_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (annotations : RecurseHeap annotation call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (topValid : annotation top)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (resident : Edges before (first :: rest))
    (closed : ClosedEdges (first :: rest)) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.large call clear fuel top first rest before = .done result after) (heap : Heap annotation before) : Heap annotation after := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have middleHeap := map_heap annotation (SourceMergedWorker.column call clear fuel)
    (fun state values => Values state values ∧ ClosedValues values)
    (fun _ _ effect _ valid => ⟨(fun value member => effect.1.available value (valid.1 value member)), valid.2⟩) columns
    (fun values _ state ready valid result final actual =>
      (SourceMergedColumns.column_done call clear fuel (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) law
        values state ready valid.1 valid.2 result final actual).1)
    (fun values _ state ready valid result final actual => column_heap annotation call annotations clear fuel values state ready valid.1 valid.2 result final actual)
    before semantic (fun column member => ⟨(by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact closed edge outer value inner)⟩) values middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeEdge annotation first.entry.key.symbol top values topValid) middle middleHeap

/-- Both actual source threshold branches preserve the physical annotation heap. -/
theorem group_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (annotations : RecurseHeap annotation call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (topValid : annotation top)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedWorker.group call clear fuel top edges before = .done results after) (heap : Heap annotation before) : Heap annotation after := by
  unfold SourceMergedWorker.group at done
  split at done
  · exact map_heap annotation (small call) (fun state edge => EdgeResident state edge ∧ ClosedValues edge.children)
      (fun _ _ effect edge valid => ⟨InternedEdgeResidency.edge_grows _ _ effect.1.growth edge valid.1, valid.2⟩) edges
      (fun edge _ state ready valid result final actual => (SourceMergedEdges.small_done call (fun _ _ => true) (fun _ _ => False) law edge state ready valid.1 valid.2 result final actual).1)
      (fun edge _ state ready valid result final actual => small_heap annotation call law annotations edge state ready valid.1 valid.2 result final actual)
      before semantic (fun edge member => ⟨resident edge member, closed edge member⟩) results after done heap
  · cases edges with
    | nil => simp at *
    | cons first rest =>
        obtain ⟨result, final, made, returned⟩ := (bind_done _ _ results after).mp done
        have finalHeap := large_heap annotation call law annotations clear fuel top topValid first rest before semantic resident closed result final made heap
        have parts := Result.done.inj returned
        cases parts.2
        exact finalHeap

/-- Actual ordered groups preserve annotations before the final node request. -/
theorem root_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (annotations : RecurseHeap annotation call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (topValid : annotation top)
    (edges : List (EdgeValue Symbol Guard)) (groups : List (List (EdgeValue Symbol Guard)))
    (grouping : MergedPhysicalGroupRoot.Grouping edges groups) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.root call clear fuel top groups before = .done result after) (heap : Heap annotation before) : Heap annotation after := by
  obtain ⟨rows, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ groups) (edge : EdgeValue Symbol Guard) (included : edge ∈ group) : edge ∈ edges :=
    grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have middleHeap := map_heap annotation (SourceMergedWorker.group call clear fuel top)
    (fun state edges => Edges state edges ∧ ClosedEdges edges)
    (fun _ _ effect _ valid => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effect.1.growth edge (valid.1 edge member)), valid.2⟩) groups
    (fun group member state ready valid result final actual =>
      (SourceMergedGroups.group_done call clear fuel (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) law top (fun _ => rfl)
        group (grouping.keys edges groups group member) state ready valid.1 valid.2 result final actual).1)
    (fun group _ state ready valid result final actual => group_heap annotation call law annotations clear fuel top topValid group state ready valid.1 valid.2 result final actual)
    before semantic (fun group member => ⟨(fun edge included => resident edge (original group member edge included)),
      (fun edge included => closed edge (original group member edge included))⟩) rows middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeNode annotation rows.flatten) middle middleHeap

/-- Every actual successful source merge worker derives annotation preservation by ordinary-fuel induction. -/
theorem worker_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupingCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (topValid : annotation top) (ordinaryFuel comparisonFuel : Nat) :
    RecurseHeap annotation (SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel) := by
  induction ordinaryFuel with
  | zero =>
      intro value before semantic available closed result after done heap
      cases value with
      | node entry edges depth free =>
          simp only [Value.free] at closed
          simp only [SourceMergedWorker.worker, closed, ite_true] at done
          cases done
      | empty | reference | mu | union =>
          have parts := Result.done.inj done
          cases parts.2
          exact heap
  | succ remaining ih =>
      intro value before semantic available closed result after done heap
      cases value with
      | node entry edges depth free =>
          have facts := semantic.ready.semantic.1.normal.facts
          have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have rowsClosed : ClosedEdges edges := fun edge member child included =>
            MergedOrdinaryHeight.closed_child before facts.coherent entry edges depth free available.resident closed edge member child included
          have law := SourceMergedSoundness.worker_done grouping groupingCorrect clear top (fun _ _ => true) (fun _ _ => False)
            (fun _ _ _ => rfl) (fun _ => rfl) remaining comparisonFuel
          exact root_heap annotation _ law ih clear comparisonFuel top topValid edges (grouping edges) (groupingCorrect edges)
            before semantic resident rowsClosed result after (by simpa only [SourceMergedWorker.worker, show free = [] from closed, ite_true] using done) heap
      | empty | reference | mu | union =>
          have parts := Result.done.inj done
          cases parts.2
          exact heap

/-- Executable source grouping and its derived ordinary height retain the physical annotation heap. -/
theorem execute_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (topValid : annotation top) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value) (closed : value.free = [])
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.execute clear top fuel value before = .done result after) (heap : Heap annotation before) : Heap annotation after :=
  worker_heap annotation MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top topValid
    (MergedOrdinaryHeight.height value) fuel value before semantic available closed result after done heap

end MicroCFTA.SourceMergedAnnotationWorker
