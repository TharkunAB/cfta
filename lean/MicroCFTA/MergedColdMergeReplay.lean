import MicroCFTA.MergedColdMergeRootBounds
import MicroCFTA.MergedSourceSelectionSemantics

/-!
# Exact replay of completed cold merges

Completed constructor requests replay in a later cache. Comparisons rerun
and derive the same answers from retained records. The complete worker
returns the same records without allocation. The proof keeps source order
and both fuel arguments.
-/
namespace MicroCFTA.MergedColdMergeReplay
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open InternedRecordCoherence InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge MergedColdMergeMapFacts
open MergedPhysicalGroupCalls MergedPhysicalGroupEdges MergedPhysicalGroupColumns MergedOrdinaryHeight Language
open MergedColdMergeRootBounds
variable {Request Output : Type}

/-- Completed ordinary constructor work replays its exact value in any later cache. -/
theorem work_replay [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Output)
    (before : State Symbol Guard) (facts : Facts before) (value : Output) (after view : State Symbol Guard)
    (done : MergedColdMerge.work computation before = .done value after) (growth : Grows after view) :
    MergedColdMerge.work computation view = .done value view := by
  have same : (run computation before).1 = value ∧ (run computation before).2 = after := by
    simpa only [MergedColdMerge.work, Result.done.injEq] using done
  have repeated := InternedConstructorTemplates.replay computation before view facts.coherent.valid (by simpa only [same.2] using growth)
  simp only [MergedColdMerge.work, repeated, same.1]

/-- A callback can replay its exact successful result without effects after completed cache growth. -/
def ValueCallReplay (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before result after view, Facts before → Prepared before → Available before value →
    call value before = .done result after → Grows after view → call value view = .done result view

/-- Ordered maps replay every completed callback at the later cache without allocations. -/
theorem map_replay (call : Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop)
    (preGrows : ∀ before after, Extension before after → ∀ request, pre before request → pre after request)
    (checked : ∀ request before result after, Facts before → Prepared before → pre before request →
      call request before = .done result after → Extension before after)
    (repeated : ∀ request before result after view, Facts before → Prepared before → pre before request →
      call request before = .done result after → Grows after view → call request view = .done result view)
    (requests : List Request) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (inputs : ∀ request ∈ requests, pre before request) (results : List Output) (after view : State Symbol Guard)
    (done : MergedColdMerge.map call requests before = .done results after) (growth : Grows after view) :
    MergedColdMerge.map call requests view = .done results view := by
  induction requests generalizing before results after with
  | nil =>
      have equal : [] = results ∧ before = after := by simpa [MergedColdMerge.map, MergedColdMerge.pure] using done
      rw [← equal.1]; rfl
  | cons request rest ih =>
      cases first : call request before with
      | failed => simp [MergedColdMerge.map, MergedColdMerge.bind, first, Result.bind] at done
      | done result middle =>
          have extension := checked request before result middle facts prepared (inputs request List.mem_cons_self) first
          have remaining := fun value member => preGrows before middle extension value (inputs value (List.mem_cons_of_mem _ member))
          cases tail : MergedColdMerge.map call rest middle with
          | failed => simp [MergedColdMerge.map, MergedColdMerge.bind, first, tail, Result.bind] at done
          | done values final =>
              have equal : result :: values = results ∧ final = after := by
                simpa [MergedColdMerge.map, MergedColdMerge.bind, first, tail, Result.bind, MergedColdMerge.pure] using done
              rcases equal with ⟨rfl, rfl⟩
              have later := (map_valid call pre (fun _ _ _ => True) preGrows (by intros; trivial)
                (fun request before result after facts prepared available done =>
                  ⟨checked request before result after facts prepared available done, trivial⟩)
                rest middle extension.facts extension.prepared remaining values final tail).1
              have headReplay := repeated request before result middle view facts prepared (inputs request List.mem_cons_self)
                first (grows_trans later.growth growth)
              have tailReplay := ih middle extension.facts extension.prepared remaining values final tail growth
              simp only [MergedColdMerge.map, MergedColdMerge.bind, headReplay, tailReplay, Result.bind, MergedColdMerge.pure]

/-- Source retained-column branches replay their actual completed constructor and recursive calls. -/
theorem retained_replay [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (repeated : ValueCallReplay recurse) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (available : Values before inputs)
    (result : Value Symbol Guard) (after view : State Symbol Guard)
    (done : retainedColumn recurse inputs before = .done result after) (growth : Grows after view) :
    retainedColumn recurse inputs view = .done result view := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values)
      (done : (if values.any recursiveBoundary then MergedColdMerge.work (makeUnion values)
        else MergedColdMerge.bind (MergedColdMerge.work (ordinaryUnion values)) recurse) before = .done result after) :
      (if values.any recursiveBoundary then MergedColdMerge.work (makeUnion values)
        else MergedColdMerge.bind (MergedColdMerge.work (ordinaryUnion values)) recurse) view = .done result view := by
    by_cases boundary : values.any recursiveBoundary = true
    · simp only [boundary, ↓reduceIte] at done ⊢
      exact work_replay _ before facts result after view done growth
    · simp only [boundary, Bool.false_eq_true, ↓reduceIte] at done ⊢
      have resident : Edges before (values.flatMap nodeEdges) := by
        intro edge member
        obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
        exact resident_edges before facts.linked value (available value included).resident edge present
      obtain ⟨extension, valid⟩ := work_valid (ordinaryUnion values) before prepared Available
        (node_verified _ before facts resident) (makeNode_noNewMu _ _)
      have called : recurse (run (ordinaryUnion values) before).1 (run (ordinaryUnion values) before).2 = .done result after := by
        simpa only [MergedColdMerge.bind, MergedColdMerge.work, Result.bind] using done
      have later := (checked _ _ result after extension.facts extension.prepared valid called).1
      have built := work_replay (ordinaryUnion values) before facts _ _ view rfl (grows_trans later.growth growth)
      have replayed := repeated _ _ result after view extension.facts extension.prepared valid called growth
      simp only [MergedColdMerge.bind, built, Result.bind, replayed]
  cases inputs with
  | nil => exact branches [] available done
  | cons first rest =>
      cases rest with
      | nil =>
          have equal : first = result ∧ before = after := by simpa [retainedColumn, MergedColdMerge.pure] using done
          simp only [retainedColumn, MergedColdMerge.pure, equal.1]
      | cons second tail => exact branches _ available done


/-- Completed constructor work retains its original cache tables. -/
theorem work_growth [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Output)
    (before : State Symbol Guard) (facts : Facts before) (value : Output) (after : State Symbol Guard)
    (done : MergedColdMerge.work computation before = .done value after) : Grows before after := by
  have same : (run computation before).1 = value ∧ (run computation before).2 = after := by
    simpa only [MergedColdMerge.work, Result.done.injEq] using done
  simpa only [same.2] using (InternedConstructorTemplates.run_correct computation before facts.coherent.valid).2

/-- A completed column replays source selection and its retained recursive result in order. -/
theorem column_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (repeated : ValueCallReplay recurse) (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (available : Values before inputs)
    (result : Value Symbol Guard) (after view : State Symbol Guard)
    (done : column recurse clear fuel inputs before = .done result after) (growth : Grows after view) :
    column recurse clear fuel inputs view = .done result view := by
  cases selected : MergedSourceSelection.select clear fuel inputs before with
  | failed => simp [column, MergedColdMerge.bind, selected, Result.bind] at done
  | done retained middle =>
      have effect := (MergedSourceSelection.select_verified clear fuel inputs before facts prepared available).effect selected
      have extension : Extension before middle := ⟨effect.facts, prepared.preserve effect.unchanged, effect.growth, effect.history⟩
      have subset := MergedSourceSelection.select_subset clear fuel inputs before retained middle selected
      have kept := fun value member => extension.available value (available value (subset value member))
      have called : retainedColumn recurse retained middle = .done result after := by
        simpa only [column, MergedColdMerge.bind, selected, Result.bind] using done
      have later := (retained_valid recurse checked retained middle extension.facts extension.prepared kept result after called).1
      have selection := MergedSourceSelectionSemantics.select_replay clear fuel inputs before facts prepared available
        retained middle view selected (grows_trans later.growth growth)
      have replayed := retained_replay recurse checked repeated retained middle extension.facts extension.prepared kept
        result after view called growth
      simp only [column, MergedColdMerge.bind, selection, Result.bind, replayed]

/-- A completed small edge replays its ordered child calls and exact edge request. -/
theorem small_replay [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (repeated : ValueCallReplay recurse) (edge : EdgeValue Symbol Guard)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : EdgeResident before edge)
    (result : EdgeValue Symbol Guard) (after view : State Symbol Guard)
    (done : small recurse edge before = .done result after) (growth : Grows after view) :
    small recurse edge view = .done result view := by
  have inputs := facts.cached.edges edge.entry.key edge resident
  cases mapped : MergedColdMerge.map recurse edge.children before with
  | failed => simp [small, MergedColdMerge.bind, mapped, Result.bind] at done
  | done values middle =>
      have extension := (values_valid recurse checked edge.children before facts prepared inputs values middle mapped).1
      have built : MergedColdMerge.work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = .done result after := by
        simpa only [small, MergedColdMerge.bind, mapped, Result.bind] using done
      have later := work_growth _ middle extension.facts result after built
      have calls := map_replay recurse Available (fun _ _ extension value available => extension.available value available)
        (fun value before result after facts prepared available done => (checked value before result after facts prepared available done).1)
        repeated edge.children before facts prepared inputs values middle view mapped (grows_trans later growth)
      have constructed := work_replay _ middle extension.facts result after view built growth
      simp only [small, MergedColdMerge.bind, calls, Result.bind, constructed]

/-- A completed large edge replays the actual source columns before the same edge request. -/
theorem large_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (repeated : ValueCallReplay recurse) (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before (first :: rest))
    (result : EdgeValue Symbol Guard) (after view : State Symbol Guard)
    (done : large recurse clear fuel top first rest before = .done result after) (growth : Grows after view) :
    large recurse clear fuel top first rest view = .done result view := by
  let requests := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have inputs : ∀ values ∈ requests, Values before values := by
    intro values member value included
    obtain ⟨row, present, inner⟩ := columns_member _ _ values member value included
    obtain ⟨edge, selected, rfl⟩ := List.mem_map.mp present
    exact facts.cached.edges edge.entry.key edge (resident edge selected) value inner
  change MergedColdMerge.bind (MergedColdMerge.map (column recurse clear fuel) requests)
    (fun values => MergedColdMerge.work (makeEdge first.entry.key.symbol top values)) before = .done result after at done
  cases mapped : MergedColdMerge.map (column recurse clear fuel) requests before with
  | failed => simp only [MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done values middle =>
      have growInputs := fun (before after : State Symbol Guard) (extension : Extension before after) values (available : Values before values) value member =>
        extension.available value (available value member)
      have callValid := fun inputs before result after facts prepared available done =>
        column_valid recurse checked clear fuel inputs before facts prepared available result after done
      have extension := (map_valid (column recurse clear fuel) Values (fun state _ value => Available state value)
        growInputs (fun _ _ extension _ value available => extension.available value available)
        callValid requests before facts prepared inputs values middle mapped).1
      have built : MergedColdMerge.work (makeEdge first.entry.key.symbol top values) middle = .done result after := by
        simpa only [MergedColdMerge.bind, mapped, Result.bind] using done
      have later := work_growth _ middle extension.facts result after built
      have calls := map_replay (column recurse clear fuel) Values growInputs
        (fun inputs before result after facts prepared available done => (callValid inputs before result after facts prepared available done).1)
        (fun inputs before result after view facts prepared available done growth =>
          column_replay recurse checked repeated clear fuel inputs before facts prepared available result after view done growth)
        requests before facts prepared inputs values middle view mapped (grows_trans later growth)
      have constructed := work_replay _ middle extension.facts result after view built growth
      simp only [large, MergedColdMerge.bind, calls, Result.bind, constructed, requests]


/-- The literal small/large threshold replays the same complete group output. -/
theorem group_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (repeated : ValueCallReplay recurse) (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (prepared : Prepared before) (resident : Edges before edges)
    (results : List (EdgeValue Symbol Guard)) (after view : State Symbol Guard)
    (done : group recurse clear fuel top edges before = .done results after) (growth : Grows after view) :
    group recurse clear fuel top edges view = .done results view := by
  by_cases few : edges.length ≤ 4
  · have mapped : MergedColdMerge.map (small recurse) edges before = .done results after := by
      simpa only [group, ite_eq_left few] using done
    have replayed := map_replay (small recurse) EdgeResident
      (fun before after extension edge resident => edge_grows before after extension.growth edge resident)
      (fun edge before result after facts prepared resident done =>
        (small_valid recurse checked edge before facts prepared resident result after done).1)
      (fun edge before result after view facts prepared resident done growth =>
        small_replay recurse checked repeated edge before facts prepared resident result after view done growth)
      edges before facts prepared resident results after view mapped growth
    simpa only [group, ite_eq_left few] using replayed
  · cases edges with
    | nil => simp at few
    | cons first rest =>
        cases built : large recurse clear fuel top first rest before with
        | failed => simp only [group, ite_eq_right few, MergedColdMerge.bind, built, Result.bind, reduceCtorEq] at done
        | done edge final =>
            have equal : [edge] = results ∧ final = after := by
              simpa only [group, ite_eq_right few, MergedColdMerge.bind, built, Result.bind, MergedColdMerge.pure, Result.done.injEq] using done
            rcases equal with ⟨rfl, rfl⟩
            simp only [group, ite_eq_right few, MergedColdMerge.bind,
              large_replay recurse checked repeated clear fuel top first rest before facts prepared resident edge final view built growth,
              Result.bind, MergedColdMerge.pure]

/-- A completed root replays the actual ordered groups and final complete node request. -/
theorem root_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (repeated : ValueCallReplay recurse) (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (buckets : List (List (EdgeValue Symbol Guard)))
    (grouping : MergedPhysicalGroupRoot.Grouping edges buckets)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before edges)
    (result : Value Symbol Guard) (after view : State Symbol Guard)
    (done : root recurse clear fuel top buckets before = .done result after) (growth : Grows after view) :
    root recurse clear fuel top buckets view = .done result view := by
  have inputs : ∀ bucket ∈ buckets, Edges before bucket ∧ SameKey bucket := by
    intro bucket member
    exact ⟨fun edge present => resident edge (grouping.partition.mem_iff.mp
      (List.mem_flatten.mpr ⟨bucket, member, present⟩)), grouping.keys edges buckets bucket member⟩
  cases mapped : MergedColdMerge.map (group recurse clear fuel top) buckets before with
  | failed => simp only [root, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done outputs middle =>
      have extension := (groups_valid recurse checked clear fuel top edges buckets grouping before facts prepared resident outputs middle mapped).1
      have built : MergedColdMerge.work (makeNode outputs.flatten) middle = .done result after := by
        simpa only [root, MergedColdMerge.bind, mapped, Result.bind] using done
      have later := work_growth _ middle extension.facts result after built
      have calls := map_replay (group recurse clear fuel top) (fun state rows => Edges state rows ∧ SameKey rows)
        (fun before after extension rows valid => ⟨fun edge member => edge_grows before after extension.growth edge (valid.1 edge member), valid.2⟩)
        (fun input before output after facts prepared valid done =>
          (group_valid recurse checked clear fuel top input valid.2 before facts prepared valid.1 output after done).1)
        (fun input before output after view facts prepared valid done growth =>
          group_replay recurse checked repeated clear fuel top input before facts prepared valid.1 output after view done growth)
        buckets before facts prepared inputs outputs middle view mapped (grows_trans later growth)
      have constructed := work_replay _ middle extension.facts result after view built growth
      simp only [root, MergedColdMerge.bind, calls, Result.bind, constructed]

/-- Induction on actual ordinary fuel derives every recursive replay certificate. -/
theorem worker_replays [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat) :
    ValueCallReplay (worker grouping clear top ordinary comparison) := by
  induction ordinary with
  | zero =>
      intro value before result after view facts prepared available done growth
      cases value with
      | empty | reference | union | mu =>
          simp only [worker, MergedColdMerge.pure, Result.done.injEq] at done
          simp only [worker, MergedColdMerge.pure, done.1]
      | node entry edges depth free =>
          by_cases closed : free = []
          · simp only [worker, ite_eq_left closed, reduceCtorEq] at done
          · simp only [worker, ite_eq_right closed, MergedColdMerge.pure, Result.done.injEq] at done
            simp only [worker, ite_eq_right closed, MergedColdMerge.pure, done.1]
  | succ remaining ih =>
      intro value before result after view facts prepared available done growth
      cases value with
      | empty | reference | union | mu =>
          simp only [worker, MergedColdMerge.pure, Result.done.injEq] at done
          simp only [worker, MergedColdMerge.pure, done.1]
      | node entry edges depth free =>
          by_cases closed : free = []
          · subst free
            exact root_replay (worker grouping clear top remaining comparison)
              (worker_valid grouping groupsCorrect clear top remaining comparison) ih clear comparison top edges
              (grouping edges) (groupsCorrect edges) before facts prepared
              (resident_edges before facts.linked _ available.resident) result after view
              (by simpa only [worker, ↓reduceIte] using done) growth
          · simp only [worker, ite_eq_right closed, MergedColdMerge.pure, Result.done.injEq] at done
            simp only [worker, ite_eq_right closed, MergedColdMerge.pure, done.1]

/-- Every completed cold worker replays the same complete record with both original fuels. -/
theorem worker_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (facts : Facts before)
    (prepared : Prepared before) (available : Available before value)
    (result : Value Symbol Guard) (after view : State Symbol Guard)
    (done : worker grouping clear top ordinary comparison value before = .done result after) (growth : Grows after view) :
    worker grouping clear top ordinary comparison value view = .done result view :=
  worker_replays grouping groupsCorrect clear top ordinary comparison value before result after view facts prepared available done growth

/-- Concrete source grouping removes all callback and grouping-law premises from worker replay. -/
theorem source_worker_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (facts : Facts before)
    (prepared : Prepared before) (available : Available before value)
    (result : Value Symbol Guard) (after view : State Symbol Guard)
    (done : worker MergedSourceGrouping.groups clear top ordinary comparison value before = .done result after)
    (growth : Grows after view) :
    worker MergedSourceGrouping.groups clear top ordinary comparison value view = .done result view :=
  worker_replay MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top ordinary comparison value
    before facts prepared available result after view done growth

/-- The source driver reuses its original height bound and exact completed comparison fuel. -/
theorem source_execute_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (comparison : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (facts : Facts before)
    (prepared : Prepared before) (available : Available before value)
    (result : Value Symbol Guard) (after view : State Symbol Guard)
    (done : execute MergedSourceGrouping.groups clear top comparison value before = .done result after)
    (growth : Grows after view) :
    execute MergedSourceGrouping.groups clear top comparison value view = .done result view :=
  source_worker_replay clear top (height value) comparison value before facts prepared available result after view done growth

end MicroCFTA.MergedColdMergeReplay
