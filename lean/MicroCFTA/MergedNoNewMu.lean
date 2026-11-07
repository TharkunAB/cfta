import MicroCFTA.MergedColdMergeRootBounds

/-!
# Stored Mu origins through actual cold merging

Every outcome retains only earlier complete Mu records.
The proof includes failed comparisons and failed recursive prefixes.
Ordinary rows and unions can still allocate non-Mu records.
This result does not bound allocation counts or native machine work.
-/
namespace MicroCFTA.MergedNoNewMu
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open MergedColdMergeMapFacts MergedColdMergeRootBounds
open MergedPhysicalGroupEdges MergedOrdinaryHeight

private def CallNoNewMu (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ input before, Facts before → Prepared before → Available before input →
    NoNewMu before (call input before).state

private theorem bind_noNewMu (first : Action Symbol Guard First)
    (next : First → Action Symbol Guard Output) (before : State Symbol Guard)
    (unchanged : NoNewMu before (first before).state)
    (later : ∀ value middle, first before = .done value middle →
      NoNewMu middle (next value middle).state) :
    NoNewMu before (MergedColdMerge.bind first next before).state := by
  unfold MergedColdMerge.bind
  cases done : first before with
  | failed fault after => simpa only [done, Result.bind, Result.state] using unchanged
  | done value middle =>
      exact noNewMu_trans (by simpa only [done, Result.state] using unchanged)
        (later value middle done)

private theorem map_noNewMu (call : Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop)
    (preGrows : ∀ before after, Extension before after → ∀ request, pre before request → pre after request)
    (checked : ∀ request before result after, Facts before → Prepared before → pre before request →
      call request before = .done result after → Extension before after)
    (unchanged : ∀ request before, Facts before → Prepared before → pre before request →
      NoNewMu before (call request before).state)
    (requests : List Request) (before : State Symbol Guard) (facts : Facts before)
    (prepared : Prepared before) (inputs : ∀ request ∈ requests, pre before request) :
    NoNewMu before (MergedColdMerge.map call requests before).state := by
  induction requests generalizing before with
  | nil => exact noNewMu_refl before
  | cons request rest ih =>
      rw [MergedColdMerge.map]
      apply bind_noNewMu _ _ before (unchanged request before facts prepared (inputs request List.mem_cons_self))
      intro value middle done
      have extension := checked request before value middle facts prepared (inputs request List.mem_cons_self) done
      apply bind_noNewMu _ _ middle
        (ih middle extension.facts extension.prepared (fun request member =>
          preGrows before middle extension request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after _
      exact noNewMu_refl after

private theorem edge_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (children : List (Value Symbol Guard)) (before : State Symbol Guard) :
    NoNewMu before (run (makeEdge symbol guard children) before).2 := by
  intro key entry body depth ordinary stored
  exact stored

private theorem retained_noNewMu [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (unchanged : CallNoNewMu recurse) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Values before inputs) : NoNewMu before (retainedColumn recurse inputs before).state := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) :
      NoNewMu before ((if values.any recursiveBoundary then MergedColdMerge.work (makeUnion values)
        else MergedColdMerge.bind (MergedColdMerge.work (ordinaryUnion values)) recurse) before).state := by
    split
    · exact makeUnion_noNewMu values before
    · have resident : Edges before (values.flatMap nodeEdges) := by
        intro edge member
        obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
        exact resident_edges before facts.linked value (available value included).resident edge present
      obtain ⟨extension, valid⟩ := work_valid (ordinaryUnion values) before prepared Available
        (node_verified _ before facts resident) (makeNode_noNewMu _ _)
      have first : NoNewMu before (run (ordinaryUnion values) before).2 :=
        makeNode_noNewMu (values.flatMap nodeEdges) before
      exact noNewMu_trans first
        (unchanged _ _ extension.facts extension.prepared valid)
  cases inputs with
  | nil => exact branches [] available
  | cons first rest =>
      cases rest with
      | nil => exact noNewMu_refl before
      | cons second tail => exact branches (first :: second :: tail) available

private theorem column_noNewMu [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (unchanged : CallNoNewMu recurse) (clear : Guard → Bool) (comparison : Nat)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Values before inputs) :
    NoNewMu before (column recurse clear comparison inputs before).state := by
  have selected := MergedSourceSelection.select_verified clear comparison inputs before facts prepared available
  unfold column
  apply bind_noNewMu _ _ before selected.unchanged
  intro retained middle done
  have effect := selected.effect done
  have subset := MergedSourceSelection.select_subset clear comparison inputs before retained middle done
  exact retained_noNewMu recurse unchanged retained middle effect.facts (prepared.preserve effect.unchanged)
    (fun value member => (available value (subset value member)).grows before middle effect.growth effect.history)

private theorem small_noNewMu [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid recurse) (unchanged : CallNoNewMu recurse)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (resident : EdgeResident before edge) :
    NoNewMu before (small recurse edge before).state := by
  have children := map_noNewMu recurse Available
    (fun _ _ extension value available => extension.available value available)
    (fun value before result after facts prepared available done =>
      (checked value before result after facts prepared available done).1)
    unchanged edge.children before facts prepared (facts.cached.edges edge.entry.key edge resident)
  unfold small
  apply bind_noNewMu _ _ before children
  intro values middle _
  exact edge_noNewMu edge.entry.key.symbol edge.entry.key.constraint values middle

private theorem large_noNewMu [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid recurse) (unchanged : CallNoNewMu recurse)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (resident : Edges before (first :: rest)) :
    NoNewMu before (large recurse clear comparison top first rest before).state := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have available : ∀ inputs ∈ columns, Values before inputs := by
    intro inputs member value included
    obtain ⟨row, present, inner⟩ := columns_member _ _ inputs member value included
    obtain ⟨edge, selected, rfl⟩ := List.mem_map.mp present
    exact facts.cached.edges edge.entry.key edge (resident edge selected) value inner
  have children := map_noNewMu (column recurse clear comparison) Values
    (fun _ _ extension _ available value member => extension.available value (available value member))
    (fun inputs before result after facts prepared available done =>
      (column_valid recurse checked clear comparison inputs before facts prepared available result after done).1)
    (fun inputs before facts prepared available =>
      column_noNewMu recurse unchanged clear comparison inputs before facts prepared available)
    columns before facts prepared available
  unfold large
  apply bind_noNewMu _ _ before children
  intro values middle _
  exact edge_noNewMu first.entry.key.symbol top values middle

private theorem group_noNewMu [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid recurse) (unchanged : CallNoNewMu recurse)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (resident : Edges before edges) :
    NoNewMu before (group recurse clear comparison top edges before).state := by
  unfold group
  split
  · exact map_noNewMu (small recurse) EdgeResident
      (fun before after extension edge resident => edge_grows before after extension.growth edge resident)
      (fun edge before result after facts prepared resident done =>
        (small_valid recurse checked edge before facts prepared resident result after done).1)
      (fun edge before facts prepared resident => small_noNewMu recurse checked unchanged edge before facts prepared resident)
      edges before facts prepared resident
  · cases edges with
    | nil => exact noNewMu_refl before
    | cons first rest =>
        apply bind_noNewMu _ _ before
          (large_noNewMu recurse checked unchanged clear comparison top first rest before facts prepared resident)
        intro edge middle _
        exact noNewMu_refl middle

private theorem root_noNewMu [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (checked : ValueCallValid recurse) (unchanged : CallNoNewMu recurse)
    (clear : Guard → Bool) (comparison : Nat) (top : Guard)
    (groups : List (List (EdgeValue Symbol Guard))) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before)
    (inputs : ∀ rows ∈ groups, Edges before rows ∧ SameKey rows) :
    NoNewMu before (root recurse clear comparison top groups before).state := by
  have mapped := map_noNewMu (group recurse clear comparison top)
    (fun state rows => Edges state rows ∧ SameKey rows)
    (fun before after extension rows valid =>
      ⟨fun edge member => edge_grows before after extension.growth edge (valid.1 edge member), valid.2⟩)
    (fun rows before result after facts prepared valid done =>
      (group_valid recurse checked clear comparison top rows valid.2 before facts prepared valid.1 result after done).1)
    (fun rows before facts prepared valid =>
      group_noNewMu recurse checked unchanged clear comparison top rows before facts prepared valid.1)
    groups before facts prepared inputs
  unfold root
  apply bind_noNewMu _ _ before mapped
  intro rows middle _
  exact makeNode_noNewMu rows.flatten middle

/-- Every actual worker outcome retains only earlier complete Mu records. -/
theorem worker_noNewMu [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat) :
    ∀ input before, Facts before → Prepared before → Available before input →
      NoNewMu before (worker grouping clear top ordinary comparison input before).state := by
  induction ordinary with
  | zero =>
      intro input before _ _ _
      cases input with
      | node entry edges depth free =>
          rw [worker]
          split <;> exact noNewMu_refl before
      | empty | reference | union | mu => exact noNewMu_refl before
  | succ ordinary ih =>
      intro input before facts prepared available
      cases input with
      | node entry edges depth free =>
          rw [worker]
          split
          · apply root_noNewMu (worker grouping clear top ordinary comparison)
              (worker_valid grouping groupsCorrect clear top ordinary comparison) ih
              clear comparison top (grouping edges) before facts prepared
            intro rows member
            refine ⟨?_, MergedPhysicalGroupRoot.Grouping.keys edges (grouping edges) (groupsCorrect edges) rows member⟩
            intro edge included
            have present := (groupsCorrect edges).partition.mem_iff.mp
              (List.mem_flatten.mpr ⟨rows, member, included⟩)
            exact resident_edges before facts.linked _ available.resident edge present
          · exact noNewMu_refl before
      | empty | reference | union | mu => exact noNewMu_refl before

/-- The executor's input-derived ordinary height preserves all stored Mu origins. -/
theorem execute_noNewMu [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (comparison : Nat)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Available before input) :
    NoNewMu before (execute grouping clear top comparison input before).state :=
  worker_noNewMu grouping groupsCorrect clear top (height input) comparison input before facts prepared available

/-- Literal source grouping needs no supplied partition or completed-worker premise. -/
theorem source_execute_noNewMu [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (comparison : Nat)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Available before input) :
    NoNewMu before (execute MergedSourceGrouping.groups clear top comparison input before).state :=
  execute_noNewMu MergedSourceGrouping.groups MergedSourceGrouping.groups_correct
    clear top comparison input before facts prepared available

end MicroCFTA.MergedNoNewMu
