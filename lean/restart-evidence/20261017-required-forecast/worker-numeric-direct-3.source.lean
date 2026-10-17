import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Required worker fuel from the initial finite requirement

The worker bound depends only on the original Needed trie. Row and child
scans share that bound. A recursive head pays one step before an ordinary
head pays the next step. Reader fuel remains a separate existential bound.
No whole-value closedness is required.
-/
namespace MicroCFTA.SourceCurrentRequiredWorkerNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache SourceEqualityRequiredWorker
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- The original requirement bounds worker depth independently of all returned heaps. -/
noncomputable def workFuel (needed : Needed) : Nat := 2 * sizeOf needed + 1

private def Replay (limit : Nat) (evaluation : Nat → Nat → Result Symbol Guard A)
    (result : A) (after : State Symbol Guard) : Prop :=
  ∃ headBound, ∀ worker reader, limit ≤ worker → headBound ≤ reader → evaluation worker reader = .done result after

private def ChildReplay (entries : List (Int × Needed)) (limit : Nat) : Prop :=
  ∀ index needed, (index, needed) ∈ entries → ∀ (value result : Value Symbol Guard) (before after : State Symbol Guard),
    RequireNode needed value before result after → SemanticReady before → CostHeap before → Available before value →
      Replay limit (fun worker reader => require worker reader needed value before) result after

private theorem children_replay (entries : List (Int × Needed)) (limit : Nat)
    (child : ChildReplay (Symbol := Symbol) (Guard := Guard) entries limit)
    {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Replay limit (fun worker reader => children (require worker reader) entries index values before) results after := by
  induction values generalizing index before results after with
  | nil => cases actual; exact ⟨0, fun _ _ _ _ => rfl⟩
  | cons value values ih =>
      cases actual with
      | unselected index absent rest =>
          obtain ⟨bound, stable⟩ := ih rest semantic costs (fun value member => available value (List.mem_cons_of_mem _ member))
          exact ⟨bound, fun worker reader enough readEnough => by
            simp only [SourceEqualityRequiredWorker.children, absent, stable worker reader enough readEnough, Result.bind]⟩
      | selected index found first rest =>
          obtain ⟨firstBound, firstDone⟩ := child _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ found)
            value _ _ _ first semantic costs (available _ List.mem_cons_self)
          have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs
            (by intro _ _ _; trivial) (available _ List.mem_cons_self)
          obtain ⟨restBound, restDone⟩ := ih rest effects.2.1 effects.2.2.1
            (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
          refine ⟨max firstBound restBound, ?_⟩
          intro worker reader enough readEnough
          simp only [SourceEqualityRequiredWorker.children, found, firstDone worker reader enough (Nat.le_trans (Nat.le_max_left _ _) readEnough),
            restDone worker reader enough (Nat.le_trans (Nat.le_max_right _ _) readEnough), Result.bind]

private theorem rows_replay (entries : List (Int × Needed)) (limit : Nat)
    (child : ChildReplay (Symbol := Symbol) (Guard := Guard) entries limit)
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges) :
    Replay limit (fun worker reader => rows (require worker reader) entries edges before) results after := by
  induction edges generalizing before results after with
  | nil => cases actual; exact ⟨0, fun _ _ _ _ => rfl⟩
  | cons edge edges ih =>
      cases actual with
      | rejected rejected rest =>
          obtain ⟨bound, stable⟩ := ih rest semantic costs (fun edge member => resident edge (List.mem_cons_of_mem _ member))
          exact ⟨bound, fun worker reader enough readEnough => by
            simp only [rows, rejected, Bool.false_eq_true, ite_false, stable worker reader enough readEnough]⟩
      | kept doesFit selected rebuilt rest =>
          have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
          obtain ⟨firstBound, firstDone⟩ := children_replay entries limit child selected semantic costs available
          have firstRows := RequireRows.kept doesFit selected rebuilt (RequireRows.nil (entries := entries))
          have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) firstRows semantic costs
            (by intro _ _ _; trivial) (by intro row member; simpa only [List.mem_singleton.mp member] using resident edge List.mem_cons_self)
          obtain ⟨restBound, restDone⟩ := ih rest effects.2.1 effects.2.2.1
            (fun row member => InternedEdgeResidency.edge_grows before _ effects.1.growth row
              (resident row (List.mem_cons_of_mem _ member)))
          refine ⟨max firstBound restBound, ?_⟩
          intro worker reader enough readEnough
          simp only [rows, doesFit, ite_true,
            firstDone worker reader enough (Nat.le_trans (Nat.le_max_left _ _) readEnough), Result.bind, work, rebuilt,
            restDone worker reader enough (Nat.le_trans (Nat.le_max_right _ _) readEnough)]

private theorem ordinary_replay (entries : List (Int × Needed))
    (child : ChildReplay (Symbol := Symbol) (Guard := Guard) entries (2 * sizeOf (Needed.node entries) - 1))
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode (.node entries) value before result after) (ordinary : Ordinary value)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Replay (2 * sizeOf (Needed.node entries))
      (fun worker reader => require worker reader (.node entries) value before) result after := by
  have positive : 0 < sizeOf (Needed.node entries) := by simp only [Needed.node.sizeOf_spec]; omega
  cases actual with
  | identity =>
      refine ⟨0, ?_⟩
      intro worker reader enough _
      cases worker with
      | zero => omega
      | succ worker => rfl
  | empty nonempty =>
      refine ⟨0, ?_⟩
      intro worker reader enough _
      cases worker with
      | zero => omega
      | succ worker => simp only [require, List.isEmpty_iff, nonempty, ite_false]
  | ordinary nonempty rowGraph rebuilt =>
      have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
      obtain ⟨bound, stable⟩ := rows_replay entries _ child rowGraph semantic costs resident
      refine ⟨bound, ?_⟩
      intro worker reader enough readEnough
      cases worker with
      | zero => omega
      | succ worker =>
          have done := stable worker reader (by omega) readEnough
          simp only [require, List.isEmpty_iff, nonempty, ite_false, done, Result.bind, work, rebuilt]
  | recursive _ recursive _ _ => cases value <;> cases recursive <;> cases ordinary

private theorem head_ordinary {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) : Ordinary result := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
      have read := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
      have ordinary := SourceEqualityOpenOrdinaryHead.node edges middle read.2.1 read.2.2.2
      simpa only [rebuilt] using ordinary.2.2.2

/-- Every actual node graph replays at a worker bound computed from its original requirement. -/
theorem node (needed : Needed) {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) :
    ∃ headBound, ∀ worker reader, workFuel needed ≤ worker → headBound ≤ reader →
      require worker reader needed value before = .done result after := by
  cases needed with
  | node entries =>
      have child : ChildReplay (Symbol := Symbol) (Guard := Guard) entries (2 * sizeOf (Needed.node entries) - 1) := by
        intro index childNeeded member value result before after graph semantic costs available
        obtain ⟨bound, stable⟩ := node childNeeded graph semantic costs available
        have smaller := List.sizeOf_lt_of_mem member
        simp only [Prod.mk.sizeOf_spec] at smaller
        refine ⟨bound, ?_⟩
        intro worker reader enough readEnough
        exact stable worker reader (by unfold workFuel; simp only [Needed.node.sizeOf_spec] at enough; omega) readEnough
      by_cases ordinary : Ordinary value
      · obtain ⟨bound, stable⟩ := ordinary_replay entries child actual ordinary semantic costs available
        exact ⟨bound, fun worker reader enough readEnough => stable worker reader (by unfold workFuel at enough; omega) readEnough⟩
      · cases actual with
        | identity =>
            refine ⟨0, ?_⟩
            intro worker reader enough _
            cases worker with
            | zero => unfold workFuel at enough; omega
            | succ worker => rfl
        | empty => exact False.elim (ordinary True.intro)
        | ordinary => exact False.elim (ordinary True.intro)
        | recursive nonempty recursive head body =>
            have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
            obtain ⟨bodyBound, bodyDone⟩ := ordinary_replay entries child body
              (head_ordinary head semantic costs available) effects.2.1 effects.2.2.1 effects.2.2.2
            obtain ⟨headBound, headDone⟩ := SourceEqualityRequiredWorkerComplete.head_stable head
            refine ⟨max bodyBound headBound, ?_⟩
            intro worker reader enough readEnough
            cases worker with
            | zero => unfold workFuel at enough; omega
            | succ worker =>
                have bodyResult := bodyDone worker reader (by unfold workFuel at enough; omega)
                  (Nat.le_trans (Nat.le_max_left _ _) readEnough)
                have headResult := headDone reader (Nat.le_trans (Nat.le_max_right _ _) readEnough)
                cases value with
                | empty | reference | node => cases recursive
                | mu | union => simp only [require, List.isEmpty_iff, nonempty, ite_false, headResult, Result.bind, bodyResult]
termination_by sizeOf needed
decreasing_by
  trace_state
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- An actual forest graph shares the original outer requirement bound across all positions. -/
theorem children (entries : List (Int × Needed)) {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) :
    ∃ headBound, ∀ worker reader, workFuel (.node entries) ≤ worker → headBound ≤ reader →
      SourceEqualityRequiredWorker.children (require worker reader) entries index values before = .done results after := by
  apply children_replay entries (workFuel (.node entries)) ?_ actual semantic costs available
  intro key needed member value result before after graph semantic costs available
  obtain ⟨bound, stable⟩ := node needed graph semantic costs available
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec] at smaller
  exact ⟨bound, fun worker reader enough readEnough => stable worker reader (by
    unfold workFuel at *; simp only [Needed.node.sizeOf_spec] at enough; omega) readEnough⟩

/-- A completed literal requireAll call replays at its initial trie-only worker bound. -/
theorem requireAll (oldFuel oldRead : Nat) (paths : List (List Int))
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll oldFuel oldRead paths values before = .done results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    ∃ headBound, ∀ worker reader, workFuel (SourceEqualityNeeded.build paths) ≤ worker → headBound ≤ reader →
      SourceEqualityRequiredExecution.requireAll worker reader paths values before = .done results after := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr ⟨oldFuel, oldRead, done⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at graph ⊢
      simpa only [SourceEqualityRequiredExecution.requireAll, compiled] using children entries graph semantic costs available

end MicroCFTA.SourceCurrentRequiredWorkerNumeric
