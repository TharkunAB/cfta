import MicroCFTA.SourceCurrentMergedHeapEffects
import MicroCFTA.MergedFreshOrdinaryComparison
import MicroCFTA.MergedColdMergeRootBounds

/-!
# Semantic readiness after completed cold merging

Prepared comparisons have the same result and cache as the fresh reader.
This equality transports the checked semantic effects through actual ordered
selection, traversal, and constructors. Stored costs do not bound total work.
-/
namespace MicroCFTA.MergedSemanticReady
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open MergedPhysicalGroupColumns MergedPhysicalGroupEdges MergedColdReaderClosedInputs
open MergedColdMergeMapFacts MergedColdMergeRootBounds MergedOrdinaryHeight
open SourceEqualityRequiredSemanticCache

private theorem any_eq [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (narrow : Value Symbol Guard)
    (wides : List (Value Symbol Guard)) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (wideClosed : ClosedValues wides) :
    SourceMergedSelection.anyAccepts clear fuel narrow wides before =
      MergedSourceSelection.anyAccepts clear fuel narrow wides before := by
  induction wides generalizing before with
  | nil => rfl
  | cons wide rest ih =>
      by_cases closed : narrow.free = []
      · have equal := MergedFreshOrdinaryComparison.check_eq clear fuel [] wide narrow before facts prepared
          (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
        have checked := MergedComparisonFacts.check_verified clear fuel [] wide narrow before facts prepared
          (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
        cases done : MergedSourceComparison.check clear fuel [] wide narrow before with
        | failed fault middle =>
            have freshDone : MergedFreshOrdinaryComparison.check clear fuel [] wide narrow before = .failed fault middle :=
              equal.trans done
            simp only [SourceMergedSelection.anyAccepts, MergedSourceSelection.anyAccepts,
              closed, ite_true, freshDone, done, Result.bind]
        | done accepted middle =>
            have freshDone : MergedFreshOrdinaryComparison.check clear fuel [] wide narrow before = .done accepted middle :=
              equal.trans done
            have effect := checked.effect done
            cases accepted with
            | true =>
                simp only [SourceMergedSelection.anyAccepts, MergedSourceSelection.anyAccepts,
                  closed, ite_true, freshDone, done, Result.bind]
            | false =>
                simpa only [SourceMergedSelection.anyAccepts, MergedSourceSelection.anyAccepts,
                  closed, ite_true, freshDone, done, Result.bind, Bool.false_eq_true, ite_false] using
                  ih middle effect.facts (prepared.preserve effect.unchanged)
                  (narrowInput.grows before middle effect.growth effect.history)
                  (fun value member => (wideInputs value (List.mem_cons_of_mem _ member)).grows
                    before middle effect.growth effect.history)
                  (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
      · simp only [SourceMergedSelection.anyAccepts, MergedSourceSelection.anyAccepts, closed, ite_false]

private theorem retain_eq [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (recursive inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (recInputs : Values before recursive) (recClosed : ClosedValues recursive)
    (available : Values before inputs) :
    SourceMergedSelection.retain clear fuel recursive inputs before =
      MergedSourceSelection.retain clear fuel recursive inputs before := by
  induction inputs generalizing before with
  | nil => rfl
  | cons child rest ih =>
      by_cases marked : closedMu child = true
      · have tail := ih before facts prepared recInputs
          (fun value member => available value (List.mem_cons_of_mem _ member))
        simpa only [SourceMergedSelection.retain, MergedSourceSelection.retain, marked, ite_true] using
          congrArg (fun result : Result Symbol Guard (List (Value Symbol Guard)) =>
            result.bind (fun retained after => .done (child :: retained) after)) tail
      · have equal := any_eq clear fuel child recursive before facts prepared
          (available child List.mem_cons_self) recInputs recClosed
        have checked := MergedSourceSelection.any_verified clear fuel child recursive before facts prepared
          (available child List.mem_cons_self) recInputs recClosed
        cases done : MergedSourceSelection.anyAccepts clear fuel child recursive before with
        | failed fault middle =>
            have freshDone : SourceMergedSelection.anyAccepts clear fuel child recursive before = .failed fault middle :=
              equal.trans done
            simp only [SourceMergedSelection.retain, MergedSourceSelection.retain,
              marked, Bool.false_eq_true, ite_false, freshDone, done, Result.bind]
        | done covered middle =>
            have freshDone : SourceMergedSelection.anyAccepts clear fuel child recursive before = .done covered middle :=
              equal.trans done
            have effect := checked.effect done
            have tail := ih middle effect.facts (prepared.preserve effect.unchanged)
              (fun value member => (recInputs value member).grows before middle effect.growth effect.history)
              (fun value member => (available value (List.mem_cons_of_mem _ member)).grows
                before middle effect.growth effect.history)
            simpa only [SourceMergedSelection.retain, MergedSourceSelection.retain,
              marked, Bool.false_eq_true, ite_false, freshDone, done, Result.bind] using
              congrArg (fun result : Result Symbol Guard (List (Value Symbol Guard)) =>
                result.bind (fun retained after => .done (if covered then retained else child :: retained) after)) tail

private theorem select_eq [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Values before inputs) :
    SourceMergedSelection.select clear fuel inputs before =
      MergedSourceSelection.select clear fuel inputs before := by
  unfold SourceMergedSelection.select MergedSourceSelection.select
  rw [retain_eq clear fuel (inputs.filter closedMu) inputs before facts prepared
    (fun value member => available value (List.mem_filter.mp member).1)
    (MergedSourceSelection.recursive_closed inputs) available]

private theorem map_eq (first second : Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop)
    (preGrows : ∀ before after, Extension before after → ∀ request,
      pre before request → pre after request)
    (checked : ∀ request before result after, Facts before → Prepared before → pre before request →
      first request before = .done result after → Extension before after)
    (agree : ∀ request before, Facts before → Prepared before → pre before request →
      second request before = first request before)
    (requests : List Request) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (inputs : ∀ request ∈ requests, pre before request) :
    MergedColdMerge.map second requests before = MergedColdMerge.map first requests before := by
  induction requests generalizing before with
  | nil => rfl
  | cons request rest ih =>
      change (second request before).bind (fun value middle =>
        (MergedColdMerge.map second rest middle).bind (fun values after => .done (value :: values) after)) =
        (first request before).bind (fun value middle =>
          (MergedColdMerge.map first rest middle).bind (fun values after => .done (value :: values) after))
      rw [agree request before facts prepared (inputs request List.mem_cons_self)]
      cases done : first request before with
      | failed => rfl
      | done value middle =>
          have extension := checked request before value middle facts prepared (inputs request List.mem_cons_self) done
          simp only [Result.bind]
          rw [ih middle extension.facts extension.prepared
            (fun request member => preGrows before middle extension request
              (inputs request (List.mem_cons_of_mem _ member)))]

private def CallEq (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ input before, Facts before → Prepared before → Available before input → second input before = first input before

private theorem retained_eq [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (agree : CallEq first second) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Values before inputs) :
    retainedColumn second inputs before = retainedColumn first inputs before := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) :
      (if values.any recursiveBoundary then work (makeUnion values)
        else MergedColdMerge.bind (work (ordinaryUnion values)) second) before =
      (if values.any recursiveBoundary then work (makeUnion values)
        else MergedColdMerge.bind (work (ordinaryUnion values)) first) before := by
    by_cases boundary : values.any recursiveBoundary = true
    · simp only [boundary, ite_true]
    · simp only [boundary, Bool.false_eq_true, ite_false, MergedColdMerge.bind, MergedColdMerge.work, Result.bind]
      have resident : Edges before (values.flatMap nodeEdges) := by
        intro edge member
        obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
        exact resident_edges before facts.linked value (available value included).resident edge present
      obtain ⟨extension, returned⟩ := work_valid (ordinaryUnion values) before prepared Available
        (node_verified _ before facts resident) (makeNode_noNewMu _ _)
      exact agree _ _ extension.facts extension.prepared returned
  cases inputs with
  | nil => exact branches [] available
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail => exact branches _ available

private theorem column_eq [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (agree : CallEq first second) (clear : Guard → Bool) (fuel : Nat)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Values before inputs) :
    SourceMergedWorker.column second clear fuel inputs before = column first clear fuel inputs before := by
  simp only [SourceMergedWorker.column, column, MergedColdMerge.bind]
  rw [select_eq clear fuel inputs before facts prepared available]
  cases selected : MergedSourceSelection.select clear fuel inputs before with
  | failed => rfl
  | done retained middle =>
      have effect := (MergedSourceSelection.select_verified clear fuel inputs before facts prepared available).effect selected
      have subset := MergedSourceSelection.select_subset clear fuel inputs before retained middle selected
      exact retained_eq first second agree retained middle effect.facts (prepared.preserve effect.unchanged)
        (fun value member => (available value (subset value member)).grows before middle effect.growth effect.history)

private theorem small_eq [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid first) (agree : CallEq first second)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (resident : EdgeResident before edge) :
    small second edge before = small first edge before := by
  simp only [small, MergedColdMerge.bind]
  rw [map_eq first second Available
    (fun _ _ extension value available => extension.available value available)
    (fun value before result after facts prepared available done =>
      (checked value before result after facts prepared available done).1)
    agree edge.children before facts prepared (facts.cached.edges edge.entry.key edge resident)]

private theorem large_eq [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid first) (agree : CallEq first second)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edge : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (resident : Edges before (edge :: rest)) :
    SourceMergedWorker.large second clear fuel top edge rest before = large first clear fuel top edge rest before := by
  let requests := MergedAlternativesGroups.columns ((edge :: rest).map EdgeValue.children) edge.children.length
  have inputs : ∀ values ∈ requests, Values before values := by
    intro values member value included
    obtain ⟨row, present, inner⟩ := columns_member _ _ values member value included
    obtain ⟨original, selected, rfl⟩ := List.mem_map.mp present
    exact facts.cached.edges original.entry.key original (resident original selected) value inner
  simp only [SourceMergedWorker.large, large, MergedColdMerge.bind]
  rw [map_eq (column first clear fuel) (SourceMergedWorker.column second clear fuel) Values
    (fun _ _ extension values available value member => extension.available value (available value member))
    (fun values before result after facts prepared available done =>
      (column_valid first checked clear fuel values before facts prepared available result after done).1)
    (fun values before facts prepared available => column_eq first second agree clear fuel values before facts prepared available)
    requests before facts prepared inputs]

private theorem group_eq [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid first) (agree : CallEq first second)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before edges) :
    SourceMergedWorker.group second clear fuel top edges before = group first clear fuel top edges before := by
  by_cases few : edges.length ≤ 4
  · simp only [SourceMergedWorker.group, group, few, ite_true]
    exact map_eq (small first) (small second) EdgeResident
      (fun before after extension edge stored => edge_grows before after extension.growth edge stored)
      (fun edge before result after facts prepared stored done =>
        (small_valid first checked edge before facts prepared stored result after done).1)
      (fun edge before facts prepared stored => small_eq first second checked agree edge before facts prepared stored)
      edges before facts prepared resident
  · simp only [SourceMergedWorker.group, group, few, ite_false]
    cases edges with
    | nil => rfl
    | cons edge rest =>
        simp only [MergedColdMerge.bind]
        rw [large_eq first second checked agree clear fuel top edge rest before facts prepared resident]

private theorem root_eq [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid first) (agree : CallEq first second)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (groups : List (List (EdgeValue Symbol Guard)))
    (grouping : MergedPhysicalGroupRoot.Grouping edges groups)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before edges) :
    SourceMergedWorker.root second clear fuel top groups before = root first clear fuel top groups before := by
  have inputs : ∀ rows ∈ groups, Edges before rows ∧ SameKey rows := by
    intro rows member
    refine ⟨?_, grouping.keys edges groups rows member⟩
    intro edge included
    exact resident edge (grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨rows, member, included⟩))
  simp only [SourceMergedWorker.root, root, MergedColdMerge.bind]
  rw [map_eq (group first clear fuel top) (SourceMergedWorker.group second clear fuel top)
    (fun state rows => Edges state rows ∧ SameKey rows)
    (fun before after extension rows valid =>
      ⟨(fun edge member => edge_grows before after extension.growth edge (valid.1 edge member)), valid.2⟩)
    (fun rows before result after facts prepared valid done =>
      (group_valid first checked clear fuel top rows valid.2 before facts prepared valid.1 result after done).1)
    (fun rows before facts prepared valid => group_eq first second checked agree clear fuel top rows before facts prepared valid.1)
    groups before facts prepared inputs]

/-- Prepared source records give the same complete or failing worker result and cache. -/
theorem worker_source_eq [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Available before input) :
    SourceMergedWorker.worker grouping clear top ordinary comparison input before =
      MergedColdMerge.worker grouping clear top ordinary comparison input before := by
  induction ordinary generalizing input before with
  | zero => cases input <;> rfl
  | succ remaining ih =>
      cases input with
      | node entry edges depth free =>
          by_cases closed : free = []
          · simp only [SourceMergedWorker.worker, MergedColdMerge.worker, closed, ite_true]
            exact root_eq _ _ (worker_valid grouping correct clear top remaining comparison)
              ih clear comparison top edges (grouping edges) (correct edges) before facts prepared
              (resident_edges before facts.linked _ available.resident)
          · simp only [SourceMergedWorker.worker, MergedColdMerge.worker, closed, ite_false]
      | empty | reference | mu | union => rfl

/-- Completed cold merging retains semantic readiness and the stored cost heap. -/
theorem worker_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (prepared : Prepared before) (available : Available before input)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : MergedColdMerge.worker grouping clear top ordinary comparison input before = .done result after) :
    SemanticReady after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Available after result := by
  have sourceDone : SourceMergedWorker.worker grouping clear top ordinary comparison input before = .done result after :=
    (worker_source_eq grouping correct clear top ordinary comparison input before
      semantic.ready.semantic.1.normal.facts prepared available).trans done
  have checked := SourceCurrentMergedHeapEffects.worker_effect (fun _ => True) grouping correct clear top
    True.intro ordinary comparison input before semantic costs available result after sourceDone
  exact ⟨checked.1.semantic, checked.1.costs, checked.2⟩

/-- A closed cold-worker input has a closed result at its actual returned cache. -/
theorem worker_closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (correct : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat)
    (input : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (prepared : Prepared before) (available : Available before input) (closed : input.free = [])
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : MergedColdMerge.worker grouping clear top ordinary comparison input before = .done result after) :
    result.free = [] := by
  have sourceDone : SourceMergedWorker.worker grouping clear top ordinary comparison input before = .done result after :=
    (worker_source_eq grouping correct clear top ordinary comparison input before
      semantic.ready.semantic.1.normal.facts prepared available).trans done
  exact (SourceMergedSoundness.worker_done grouping correct clear top
    (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) (fun _ => rfl)
    ordinary comparison input before semantic available closed result after sourceDone).2.closed

/-- Literal executable grouping retains the same returned-state readiness. -/
theorem execute_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (comparison : Nat)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (prepared : Prepared before) (available : Available before input)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : MergedColdMerge.execute MergedSourceGrouping.groups clear top comparison input before = .done result after) :
    SemanticReady after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Available after result :=
  worker_ready MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top
    (MergedOrdinaryHeight.height input) comparison input before semantic costs prepared available result after done

/-- Literal executable grouping preserves closed inputs at every completed bound. -/
theorem execute_closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (comparison : Nat)
    (input : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (prepared : Prepared before) (available : Available before input) (closed : input.free = [])
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : MergedColdMerge.execute MergedSourceGrouping.groups clear top comparison input before = .done result after) : result.free = [] :=
  worker_closed MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top
    (MergedOrdinaryHeight.height input) comparison input before semantic prepared available closed result after done

/-- Actual source grouping retains readiness, stored costs, availability, and closed inputs. -/
theorem source_execute_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (comparison : Nat)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (prepared : Prepared before) (available : Available before input)
    (done : MergedColdMerge.execute MergedSourceGrouping.groups clear top comparison input before = .done result after) :
    SemanticReady after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧ Available after result ∧
      (input.free = [] → result.free = []) := by
  have checked := execute_ready clear top comparison input before semantic costs prepared available result after done
  exact ⟨checked.1, checked.2.1, checked.2.2, fun closed =>
    execute_closed clear top comparison input before semantic prepared available closed result after done⟩

end MicroCFTA.MergedSemanticReady
