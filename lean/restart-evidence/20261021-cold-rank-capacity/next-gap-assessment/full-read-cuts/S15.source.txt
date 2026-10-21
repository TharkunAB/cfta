import MicroCFTA.EqualityMergedTargetNormalization
import MicroCFTA.EqualityMergedTargetReadback

/-!
# Exact fixed points of repeated ordinary target merging

The original ordinary height bounds repeated merge calls on finite
ordinary trees. After that many calls, every traversed root has small
groups and exact constructor readback. The next call returns the same
complete value and the same actual cache at every comparison fuel.

This proves target normalization. The full equality schedule also performs
intersection and endpoint edits; its general fixed-point bound is separate.
-/
namespace MicroCFTA.EqualityMergedTargetFixedPoint
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge MergedSourceGrouping MergedOrdinaryHeight
open EqualityMergedTargetLayers EqualityMergedTargetHeight EqualityMergedTargetNormalization
open EqualityMergedTargetReadback

/-- A traversed root has small full-key groups and a verified immutable constructor readback. -/
def Exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (value : Value Symbol Guard) : Prop :=
  Good value ∧ ∀ entry edges depth, value = .node entry edges depth [] → Replayable value

/-- Height-zero boundaries need no ordinary constructor replay. -/
theorem boundary_exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (value : Value Symbol Guard) (zero : height value = 0) : Exact value := by
  refine ⟨boundary_good value zero, ?_⟩
  intro entry edges depth same
  subst value
  simp [height] at zero

/-- Actual successful closed root construction establishes both exact root obligations. -/
theorem step_exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (input result : Value Symbol Guard)
    (step : Step clear top input result) : Exact result := by
  refine ⟨step_root clear top input result step, ?_⟩
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
        have normal := MergedColdMergeRootBounds.worker_root_normal clear top ordinary comparison entry edges depth
          before facts prepared available result after done
        obtain ⟨extension, resultAvailable⟩ := MergedColdMergeMapFacts.worker_valid groups groups_correct clear top ordinary comparison
          _ before result after facts prepared available done
        intro other rows level same
        exact ⟨after, extension.facts, resultAvailable, normal⟩
      · cases ordinary <;>
          simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure, Result.done.injEq] at done <;>
          rcases done with ⟨rfl, rfl⟩ <;>
          intro other rows level same <;>
          cases same <;>
          contradiction

/-- Actual source shape also advances exact constructor normalization one ordinary layer per pass. -/
theorem source_exact_shape [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) :
    Shape (Step (Symbol := Symbol) clear top) (Exact (Symbol := Symbol) (Guard := Guard)) :=
  ⟨step_exact clear top, fun input result step exact child member =>
    (source_shape clear top).smallChildren input result step exact.1 child member⟩

/-- Original ordinary height bounds exact normalization of every traversed root. -/
theorem source_exact_normal [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (count : Nat) (input result : Value Symbol Guard)
    (trace : Trace (Step clear top) count input result) (enough : height input ≤ count) : Normal Exact result :=
  trace_normal (Step clear top) Exact (source_exact_shape clear top) boundary_exact (source_height clear top)
    count input result trace enough

/-- Ordered maps of exact no-effect callbacks return the same ordered input list and cache. -/
theorem map_fixed (call : Input → Action Symbol Guard Input) (inputs : List Input)
    (state : State Symbol Guard) (fixed : ∀ input ∈ inputs, call input state = .done input state) :
    MergedColdMerge.map call inputs state = .done inputs state := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      simp only [MergedColdMerge.map, MergedColdMerge.bind, fixed input List.mem_cons_self, Result.bind,
        ih (fun value member => fixed value (List.mem_cons_of_mem _ member)), MergedColdMerge.pure]

/-- A resident complete edge reconstructs from its exact requested fields without cache effects. -/
theorem edge_replay [DecidableEq (EdgeKey Symbol Guard)] (edge : EdgeValue Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (resident : EdgeResident state edge) :
    run (makeEdge edge.entry.key.symbol edge.entry.key.constraint edge.children) state = (edge, state) := by
  obtain ⟨table, fields⟩ := facts.coherent.edges edge.entry.key edge resident
  have keyEq : EdgeKey.mk edge.entry.key.symbol (edge.children.map Value.referenceOf) edge.entry.key.constraint = edge.entry.key := by
    cases key : edge.entry.key
    simp_all only [EdgeFields]
  change state.edgeRecords edge.entry.key = some edge at resident
  simp only [makeEdge, run, edgeStep, keyEq, Cache.intern, table, Cache.keepFirst, resident, Option.getD_some]

/-- A recursively exact target returns the same complete value and actual cache at sufficient ordinary fuel. -/
theorem worker_fixed [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat)
    (value : Value Symbol Guard) (enough : height value ≤ ordinary) (normal : Normal Exact value)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    worker groups clear top ordinary comparison value state = .done value state := by
  induction ordinary generalizing value state with
  | zero =>
      cases value <;> try rfl
      simp [height] at enough
  | succ ordinary ih =>
      cases value with
      | empty | reference | union | mu => rfl
      | node entry edges depth free =>
          by_cases closed : free = []
          · subst free
            cases normal with
            | intro exact below =>
                have original : ∀ group ∈ groups edges, ∀ edge ∈ group, edge ∈ edges := by
                  intro group present edge member
                  exact (groups_correct edges).partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, present, member⟩)
                have smallFixed : ∀ edge ∈ edges, small (worker groups clear top ordinary comparison) edge state = .done edge state := by
                  intro edge member
                  have resident := resident_edges state facts.linked _ available.resident edge member
                  have mapped := map_fixed (worker groups clear top ordinary comparison) edge.children state (fun child included =>
                    ih child (by have smaller := child_lt entry edges depth [] edge member child included; simp only [height] at enough smaller; omega)
                      (below child (by simp only [EqualityMergedTargetLayers.children, ↓reduceIte]; exact List.mem_flatMap.mpr ⟨edge, member, included⟩))
                      state facts prepared (facts.cached.edges edge.entry.key edge resident child included))
                  simp only [small, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, edge_replay edge state facts resident]
                have groupFixed : ∀ group ∈ groups edges,
                    MergedColdMerge.group (worker groups clear top ordinary comparison) clear comparison top group state = .done group state := by
                  intro group member
                  simpa only [MergedColdMerge.group, ite_eq_left (good_groups entry edges depth exact.1 group member)] using
                    map_fixed (small (worker groups clear top ordinary comparison)) group state
                      (fun edge included => smallFixed edge (original group member edge included))
                have mapped := map_fixed _ (groups edges) state groupFixed
                have rowsResident : Edges state edges := resident_edges state facts.linked _ available.resident
                have sameRequest : makeNode (groups edges).flatten = makeNode edges := by
                  apply InternedNodeSetCongruence.makeNode_same_members state facts.coherent _ _
                    (fun edge member => rowsResident edge ((groups_correct edges).partition.mem_iff.mp member)) rowsResident
                  intro edge
                  simp only [surviving, List.mem_filter, (groups_correct edges).partition.mem_iff]
                have readback := replayable_normal _ (exact.2 entry edges depth rfl) state facts available
                simpa only [worker, ↓reduceIte, root, MergedColdMerge.bind, mapped, Result.bind,
                  MergedColdMerge.work, sameRequest, nodeEdges] using congrArg (fun pair => Result.done pair.1 pair.2) readback
          · simp only [worker, closed, ↓reduceIte, MergedColdMerge.pure]

/-- Every comparison-fuel choice returns a recursively exact target without any cache effect. -/
theorem execute_fixed [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (comparison : Nat) (value : Value Symbol Guard)
    (normal : Normal Exact value) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    execute groups clear top comparison value state = .done value state :=
  worker_fixed clear top (height value) comparison value (Nat.le_refl _) normal state facts prepared available

/-- Actual ordinary target merging reaches an exact fixed point within the original ordinary height. -/
theorem fixed_point_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (available : Available before input) (tree : Tree input) :
    ∃ result after, Runs clear top (height input) input before result after ∧
      Extension before after ∧ Available after result ∧ Tree result ∧
      ∀ comparison, execute groups clear top comparison result after = .done result after := by
  obtain ⟨result, after, runs, extension, resultAvailable⟩ := runs_exist clear top (height input) input before facts prepared available
  obtain ⟨_, _, resultTree, trace⟩ := runs_valid clear top (height input) input before result after facts prepared available tree runs
  have normal := source_exact_normal clear top (height input) input result trace (Nat.le_refl _)
  exact ⟨result, after, runs, extension, resultAvailable, resultTree,
    fun comparison => execute_fixed clear top comparison result normal after extension.facts extension.prepared resultAvailable⟩

end MicroCFTA.EqualityMergedTargetFixedPoint
