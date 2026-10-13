import MicroCFTA.EqualityMergedTargetHeight
import MicroCFTA.MergedColdMergeRootBounds

/-!
# Derived multi-pass normalization of finite ordinary targets

Every actual merge call normalizes the root group counts. Small roots
map original children through actual recursive calls. The derived height
bound makes the original ordinary height sufficient to normalize all
ordinary group counts. Runtime traces retain their actual cache sequence.

This result concerns repeated target merging. It does not assert a bound
for the intersection and endpoint edits of a complete equality schedule.
-/
namespace MicroCFTA.EqualityMergedTargetNormalization
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge MergedSourceGrouping MergedOrdinaryHeight
open EqualityMergedTargetLayers EqualityMergedTargetHeight

/-- Every full symbol/arity class at a traversed ordinary root has at most four rows. -/
def Good [DecidableEq Symbol] (value : Value Symbol Guard) : Prop :=
  ∀ entry edges depth, value = .node entry edges depth [] →
    ∀ key, (edges.filter (fun edge => decide (groupKey edge = key))).length ≤ 4

/-- A height-zero boundary has no traversed ordinary root. -/
theorem boundary_good [DecidableEq Symbol] (value : Value Symbol Guard) (zero : height value = 0) : Good value := by
  intro entry edges depth same
  subst value
  simp [height] at zero

/-- Actual group enumeration converts the full-key bound to the literal small-group branch. -/
theorem good_groups [DecidableEq Symbol] (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (good : Good (.node entry edges depth [])) :
    ∀ group ∈ groups edges, group.length ≤ 4 := by
  intro group member
  obtain ⟨first, rest, same, full⟩ := groups_exact groupKey edges group member
  rw [full]
  exact good entry edges depth rfl (groupKey first)

/-- Each transition is an actual successful prepared merge of a finite ordinary input tree. -/
def Step [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (input result : Value Symbol Guard) : Prop :=
  Tree input ∧ EqualityMergedTargetShape.Merge groups clear top input result

/-- Every successful source target merge establishes the actual complete root-group bound. -/
theorem step_root [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (input result : Value Symbol Guard)
    (step : Step clear top input result) : Good result := by
  obtain ⟨tree, ordinary, comparison, before, after, facts, prepared, available, done⟩ := step
  cases tree with
  | empty =>
      cases ordinary <;>
        simp only [worker, MergedColdMerge.pure, Result.done.injEq] at done <;>
        rcases done with ⟨rfl, rfl⟩ <;>
        intro entry edges depth impossible <;>
        cases impossible
  | node entry edges depth free trees =>
      by_cases closed : free = []
      · subst free
        have bound := MergedColdMergeRootBounds.worker_root_bound clear top ordinary comparison entry edges depth
          before facts prepared available result after done
        intro other rows level same key
        subst result
        exact bound key
      · cases ordinary <;>
          simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done <;>
          rcases done with ⟨rfl, rfl⟩ <;>
          intro other rows level same <;>
          cases same <;>
          contradiction

/-- Both layer-shape obligations follow from actual source execution, with no callback assumptions. -/
theorem source_shape [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) :
    Shape (Step (Symbol := Symbol) clear top) (Good (Symbol := Symbol) (Guard := Guard)) := by
  refine ⟨step_root clear top, ?_⟩
  intro input result step good child member
  obtain ⟨original, included, called⟩ := EqualityMergedTargetShape.worker_small_children groups groups_correct
    clear top input result step.2
    (fun entry edges depth same => good_groups entry edges depth (same ▸ good)) child member
  refine ⟨original, included, ?_, called⟩
  cases input with
  | empty | reference | union | mu => simp [EqualityMergedTargetLayers.children] at included
  | node entry edges depth free =>
      simp only [EqualityMergedTargetLayers.children] at included
      split at included
      · obtain ⟨edge, present, inner⟩ := List.mem_flatMap.mp included
        exact tree_child _ step.1 edge present original inner
      · contradiction

/-- Every actual ordinary source transition satisfies the height premise of the layer theorem. -/
theorem source_height [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (input result : Value Symbol Guard)
    (step : Step clear top input result) : height result ≤ height input :=
  (merge_height groups groups_correct clear top input result step.1 step.2).2

/-- The original ordinary height bounds all recursive group-count normalization passes. -/
theorem source_normal [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (count : Nat) (input result : Value Symbol Guard)
    (trace : Trace (Step clear top) count input result) (enough : height input ≤ count) : Normal Good result :=
  trace_normal (Step clear top) Good (source_shape clear top) boundary_good (source_height clear top)
    count input result trace enough

/-- Successive source executions thread the actual returned value and constructor cache. -/
inductive Runs [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) :
    Nat → Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop where
  | nil (value state) : Runs clear top 0 value state value state
  | snoc {count input before middle current result after} (previous : Runs clear top count input before middle current)
      (fuel : Nat) (done : execute groups clear top fuel middle current = .done result after) :
      Runs clear top (count + 1) input before result after

/-- Every completed runtime trace retains source invariants and supplies the proved structural trace. -/
theorem runs_valid [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (count : Nat) (input : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Available before input) (tree : Tree input) (runs : Runs clear top count input before result after) :
    Extension before after ∧ Available after result ∧ Tree result ∧ Trace (Step clear top) count input result := by
  induction runs with
  | nil => exact ⟨.refl _ facts prepared, available, tree, .nil _⟩
  | @snoc count input before middle current result after previous fuel done ih =>
      obtain ⟨extension, middleAvailable, middleTree, trace⟩ := ih facts prepared available tree
      have called : EqualityMergedTargetShape.Merge groups clear top middle result :=
        ⟨height middle, fuel, current, after, extension.facts, extension.prepared, middleAvailable, done⟩
      obtain ⟨later, resultAvailable⟩ := MergedColdMergeMapFacts.worker_valid groups groups_correct clear top (height middle) fuel
        middle current result after extension.facts extension.prepared middleAvailable done
      exact ⟨extension.trans later, resultAvailable,
        (merge_height groups groups_correct clear top middle result middleTree called).1,
        .snoc trace ⟨middleTree, called⟩⟩

/-- Every finite number of actual calls completes from a prepared available ordinary source input. -/
theorem runs_exist [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (count : Nat) (input : Value Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Available before input) :
    ∃ result after, Runs clear top count input before result after ∧ Extension before after ∧ Available after result := by
  induction count with
  | zero => exact ⟨input, before, .nil _ _, .refl before facts prepared, available⟩
  | succ count ih =>
      obtain ⟨middle, current, previous, extension, middleAvailable⟩ := ih
      obtain ⟨bound, result, after, done, later, resultAvailable⟩ :=
        source_execute_complete clear top middle current extension.facts extension.prepared middleAvailable
      exact ⟨result, after, .snoc previous bound (done bound (Nat.le_refl _)), extension.trans later, resultAvailable⟩

/-- A completed actual source trace reaches fully normalized ordinary group counts within original height. -/
theorem normalization_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Available before input) (tree : Tree input) :
    ∃ result after, Runs clear top (height input) input before result after ∧
      Extension before after ∧ Available after result ∧ Tree result ∧ Normal Good result := by
  obtain ⟨result, after, runs, extension, resultAvailable⟩ := runs_exist clear top (height input) input before facts prepared available
  obtain ⟨_, _, resultTree, trace⟩ := runs_valid clear top (height input) input before result after facts prepared available tree runs
  exact ⟨result, after, runs, extension, resultAvailable, resultTree,
    source_normal clear top (height input) input result trace (Nat.le_refl _)⟩

end MicroCFTA.EqualityMergedTargetNormalization
