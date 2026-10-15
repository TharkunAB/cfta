import MicroCFTA.SourceMergedProbeSelection
import MicroCFTA.SourceMergedSoundness

/-!
# Filtered Mu probe heaps through actual general source merging

The proof retains the actual comparison filter, recursive boundary test,
four-row threshold, original small-row guards, and large-row Top guard.
Existing source effects derive each intermediate scope. The proof follows
those requests and does not assume a complete output invariant.
-/
namespace MicroCFTA.SourceMergedProbeWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (Effect bind_done)
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure bind work map retainedColumn small)
open SourceMergedContracts
open InternedFreshOrdinaryProbeHeap (Heap)

/-- Recursive preservation is required only at actual successful closed calls. -/
def RecurseHeap (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before, SemanticReady before → Available before value → value.free = [] →
    ∀ result after, call value before = .done result after → Heap before → Heap after

/-- Ordered maps retain probes through the actual effects of each earlier request. -/
theorem map_heap (call : Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (requests : List Request)
    (effects : ∀ request ∈ requests, ∀ before, SemanticReady before → pre before request →
      ∀ result after, call request before = .done result after → Effect before after)
    (probes : ∀ request ∈ requests, ∀ before, SemanticReady before → pre before request →
      ∀ result after, call request before = .done result after → Heap before → Heap after)
    (before : State Symbol Guard) (semantic : SemanticReady before) (inputs : ∀ request ∈ requests, pre before request)
    (results : List Output) (after : State Symbol Guard) (done : map call requests before = .done results after)
    (heap : Heap before) : Heap after := by
  induction requests generalizing before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact heap
  | cons request requests ih =>
      obtain ⟨first, middle, called, later⟩ := (bind_done _ _ results after).mp done
      have checked := effects request List.mem_cons_self before semantic (inputs request List.mem_cons_self) first middle called
      have middleHeap := probes request List.mem_cons_self before semantic (inputs request List.mem_cons_self) first middle called heap
      obtain ⟨rest, final, mapped, returned⟩ := (bind_done _ _ results after).mp later
      have finalHeap := ih (fun request member => effects request (List.mem_cons_of_mem _ member))
        (fun request member => probes request (List.mem_cons_of_mem _ member)) middle checked.2
        (fun request member => preGrows before middle checked request (inputs request (List.mem_cons_of_mem _ member))) rest final mapped middleHeap
      have parts := Result.done.inj returned
      cases parts.2
      exact finalHeap

/-- Every retained-column branch preserves probes through literal union work and actual recursion. -/
theorem retained_heap [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (probes : RecurseHeap call)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn call inputs before = .done result after) (heap : Heap before) : Heap after := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values)
      (done : (if values.any MergedOrdinaryHeight.recursiveBoundary then work (makeUnion values)
        else bind (work (MergedOrdinaryHeight.ordinaryUnion values)) call) before = .done result after) : Heap after := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true, work] at done
      have parts := Result.done.inj done
      cases parts.2
      exact InternedFreshOrdinaryProbeHeap.union values before heap
    · simp only [boundary, Bool.false_eq_true, ite_false] at done
      obtain ⟨united, middle, constructed, called⟩ := (bind_done _ _ result after).mp done
      have parts := Result.done.inj constructed
      cases parts.1; cases parts.2
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      exact probes _ _ checked.1.2 checked.2.1 checked.2.2.1 result after called
        (InternedFreshOrdinaryProbeHeap.node _ before heap)
  cases inputs with
  | nil => exact branches [] available closed done
  | cons first rest =>
      cases rest with
      | nil =>
          have parts := Result.done.inj done
          cases parts.2
          exact heap
      | cons second rest => exact branches (first :: second :: rest) available closed done

/-- The actual repaired child filter and retained-column requests preserve probes in order. -/
theorem column_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (probes : RecurseHeap call)
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before inputs) (closed : ClosedValues inputs)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.column call clear fuel inputs before = .done result after) (heap : Heap before) : Heap after := by
  obtain ⟨selected, middle, filtered, called⟩ := (bind_done _ _ result after).mp done
  have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
    (fun _ _ _ => rfl) inputs before semantic available closed selected middle filtered
  have filteredHeap := (SourceMergedProbeSelection.select_effect clear fuel inputs before semantic available closed selected middle filtered).probes heap
  exact retained_heap call probes selected middle checked.1.2 checked.2.1 checked.2.2.1 result after called filteredHeap

/-- Small rows preserve filtered probes through ordered children and original guards. -/
theorem small_heap [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (probes : RecurseHeap call)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : EdgeResident before edge) (closed : ClosedValues edge.children) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) (heap : Heap before) : Heap after := by
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  have middleHeap := map_heap call (fun state value => Available state value ∧ value.free = [])
    (fun _ _ effect value valid => ⟨effect.1.available value valid.1, valid.2⟩) edge.children
    (fun value _ state ready valid result final actual => (law value state ready valid.1 valid.2 result final actual).1)
    (fun value _ state ready valid result final actual => probes value state ready valid.1 valid.2 result final actual)
    before semantic (fun value member => ⟨available value member, closed value member⟩) values middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact InternedFreshOrdinaryProbeHeap.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleHeap

/-- Large groups preserve filtered probes through actual columns and literal Top. -/
theorem large_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (probes : RecurseHeap call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (resident : Edges before (first :: rest))
    (closed : ClosedEdges (first :: rest)) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.large call clear fuel top first rest before = .done result after) (heap : Heap before) : Heap after := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have middleHeap := map_heap (SourceMergedWorker.column call clear fuel)
    (fun state values => Values state values ∧ ClosedValues values)
    (fun _ _ effect _ valid => ⟨(fun value member => effect.1.available value (valid.1 value member)), valid.2⟩) columns
    (fun values _ state ready valid result final actual =>
      (SourceMergedColumns.column_done call clear fuel (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) law
        values state ready valid.1 valid.2 result final actual).1)
    (fun values _ state ready valid result final actual => column_heap call probes clear fuel values state ready valid.1 valid.2 result final actual)
    before semantic (fun column member => ⟨(by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact closed edge outer value inner)⟩) values middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact InternedFreshOrdinaryProbeHeap.edge first.entry.key.symbol top values middle middleHeap

/-- Both actual source threshold branches preserve the probe invariant. -/
theorem group_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (probes : RecurseHeap call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedWorker.group call clear fuel top edges before = .done results after) (heap : Heap before) : Heap after := by
  unfold SourceMergedWorker.group at done
  split at done
  · exact map_heap (small call) (fun state edge => EdgeResident state edge ∧ ClosedValues edge.children)
      (fun _ _ effect edge valid => ⟨InternedEdgeResidency.edge_grows _ _ effect.1.growth edge valid.1, valid.2⟩) edges
      (fun edge _ state ready valid result final actual => (SourceMergedEdges.small_done call (fun _ _ => true) (fun _ _ => False) law edge state ready valid.1 valid.2 result final actual).1)
      (fun edge _ state ready valid result final actual => small_heap call law probes edge state ready valid.1 valid.2 result final actual)
      before semantic (fun edge member => ⟨resident edge member, closed edge member⟩) results after done heap
  · cases edges with
    | nil => simp at *
    | cons first rest =>
        obtain ⟨result, final, made, returned⟩ := (bind_done _ _ results after).mp done
        have finalHeap := large_heap call law probes clear fuel top first rest before semantic resident closed result final made heap
        have parts := Result.done.inj returned
        cases parts.2
        exact finalHeap

/-- Actual ordered groups preserve probes before the final node request. -/
theorem root_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (probes : RecurseHeap call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (groups : List (List (EdgeValue Symbol Guard)))
    (grouping : MergedPhysicalGroupRoot.Grouping edges groups) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.root call clear fuel top groups before = .done result after) (heap : Heap before) : Heap after := by
  obtain ⟨rows, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ groups) (edge : EdgeValue Symbol Guard) (included : edge ∈ group) : edge ∈ edges :=
    grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have middleHeap := map_heap (SourceMergedWorker.group call clear fuel top)
    (fun state edges => Edges state edges ∧ ClosedEdges edges)
    (fun _ _ effect _ valid => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effect.1.growth edge (valid.1 edge member)), valid.2⟩) groups
    (fun group member state ready valid result final actual =>
      (SourceMergedGroups.group_done call clear fuel (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) law top (fun _ => rfl)
        group (grouping.keys edges groups group member) state ready valid.1 valid.2 result final actual).1)
    (fun group _ state ready valid result final actual => group_heap call law probes clear fuel top group state ready valid.1 valid.2 result final actual)
    before semantic (fun group member => ⟨(fun edge included => resident edge (original group member edge included)),
      (fun edge included => closed edge (original group member edge included))⟩) rows middle mapped heap
  have parts := Result.done.inj made
  cases parts.2
  exact InternedFreshOrdinaryProbeHeap.node rows.flatten middle middleHeap

/-- Every actual successful source merge worker derives preservation by ordinary-fuel induction. -/
theorem worker_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupingCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard)  (ordinaryFuel comparisonFuel : Nat) :
    RecurseHeap (SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel) := by
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
          exact root_heap _ law ih clear comparisonFuel top edges (grouping edges) (groupingCorrect edges)
            before semantic resident rowsClosed result after (by simpa only [SourceMergedWorker.worker, show free = [] from closed, ite_true] using done) heap
      | empty | reference | mu | union =>
          have parts := Result.done.inj done
          cases parts.2
          exact heap

/-- Executable source grouping and its derived ordinary height retain the probe invariant. -/
theorem execute_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard)  (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value) (closed : value.free = [])
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.execute clear top fuel value before = .done result after) (heap : Heap before) : Heap after :=
  worker_heap MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top
    (MergedOrdinaryHeight.height value) fuel value before semantic available closed result after done heap

end MicroCFTA.SourceMergedProbeWorker
