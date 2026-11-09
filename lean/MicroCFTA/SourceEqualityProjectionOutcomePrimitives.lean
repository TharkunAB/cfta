import MicroCFTA.SourceEqualityProjectionMemos
import MicroCFTA.SourceEqualityProjectionWorker

/-!
# Unfolding receipts for every primitive projection outcome

Each receipt retains the actual ordered exposure calls. Failed reads keep
the returned heap and memo. Head and union constructors add no unfolding
call. Current semantic heaps, cost heaps, and residency derive the result
invariants. The input need not be closed. This module does not prove that
an exposure or a projection succeeds.
-/
namespace MicroCFTA.SourceEqualityProjectionOutcomePrimitives
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredWorker (Result work)
open SourceEqualityProjectionWorker (readAll union)
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo
local notation "Correct" => InternedFreshOrdinaryUnfoldMemo.Correct
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Every worker outcome retains its actual returned constructor heap. -/
def reached (actual : Result Symbol Guard A) : State Symbol Guard :=
  match actual with
  | .done _ after | .pending _ after | .unresolved _ after | .exhausted _ after => after

/-- Ordered operand reads stop at the first actual exposure failure. -/
inductive ReadAllReads [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → List (Value Symbol Guard) → State Symbol Guard →
      UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | nil : ReadAllReads h [] before memo memo
  | cons (actual : MergedFreshOrdinaryExposure.nodeEdges h value before = .done edges middle)
      (first : SourceEqualityExposureMemos.NodeEdgesReads h value before memo middleMemo)
      (rest : ReadAllReads h values middle middleMemo saved) :
      ReadAllReads h (value :: values) before memo saved
  | pending (actual : MergedFreshOrdinaryExposure.nodeEdges h value before = .pending key after)
      (calls : SourceEqualityExposureMemos.NodeEdgesReads h value before memo saved) :
      ReadAllReads h (value :: values) before memo saved
  | unresolved (actual : MergedFreshOrdinaryExposure.nodeEdges h value before = .unresolved name after)
      (calls : SourceEqualityExposureMemos.NodeEdgesReads h value before memo saved) :
      ReadAllReads h (value :: values) before memo saved
  | exhausted (actual : MergedFreshOrdinaryExposure.nodeEdges h value before = .exhausted after)
      (calls : SourceEqualityExposureMemos.NodeEdgesReads h value before memo saved) :
      ReadAllReads h (value :: values) before memo saved

/-- Head reconstruction retains its sole exposure, including every fallback call. -/
inductive HeadReads [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Value Symbol Guard → State Symbol Guard → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | read (calls : SourceEqualityExposureMemos.NodeEdgesReads h value before memo saved) :
      HeadReads h value before memo saved

/-- Union reconstruction retains the actual ordered operand exposures. -/
inductive UnionReads [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → List (Value Symbol Guard) → State Symbol Guard → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | read (calls : ReadAllReads h values before memo saved) : UnionReads h values before memo saved

private theorem mapped_reached (actual : Result Symbol Guard A) (f : A → B) :
    reached (actual.bind fun value after => .done (f value) after) = reached actual := by
  cases actual <;> rfl

private theorem node_effects [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) :
    Keeps before (run (makeNode edges) before).2 ∧ SemanticReady (run (makeNode edges) before).2 ∧
      CostHeap (run (makeNode edges) before).2 ∧
      Available (run (makeNode edges) before).2 (run (makeNode edges) before).1 := by
  have checked := SourceEqualityOpenOrdinaryHead.node edges before semantic resident
  exact ⟨checked.1, checked.2.1,
    InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeNode_noNewMu edges before),
    checked.2.2.1⟩

private theorem node_correct [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (resident : Edges before edges)
    (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    Correct (run (makeNode edges) before).2 memo := by
  have checked := SourceEqualityOpenOrdinaryHead.node edges before semantic resident
  exact InternedFreshOrdinaryUnfoldMemo.grows before _ semantic.ready.semantic.1.normal.facts.coherent.valid
    checked.1.growth checked.1.history memo correct

/-- All ordered-read outcomes retain current heaps; completed rows are resident. -/
theorem readAll_effects [DecidableEq (EdgeKey Symbol Guard)] (h : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Keeps before (reached (readAll h values before)) ∧ SemanticReady (reached (readAll h values before)) ∧
      CostHeap (reached (readAll h values before)) ∧
      ∀ edges after, readAll h values before = .done edges after → Edges after edges := by
  induction values generalizing before with
  | nil =>
      refine ⟨pure_keeps before semantic.ready, semantic, costs, ?_⟩
      intro edges after completed
      cases completed
      exact fun _ member => False.elim (List.not_mem_nil member)
  | cons value values ih =>
      have first := SourceEqualityExposureCosts.nodeEdges_verified h value before semantic costs
        (available value List.mem_cons_self)
      cases read : MergedFreshOrdinaryExposure.nodeEdges h value before with
      | done edges middle =>
          have own := SourceEqualityProjectionCosts.read_effects (.done h read) semantic costs
            (available value List.mem_cons_self)
          have later := ih middle own.2.1 own.2.2.1
            (fun child member => own.1.available child (available child (List.mem_cons_of_mem _ member)))
          refine ⟨by simpa only [readAll, read, mapped_reached] using own.1.trans later.1,
            by simpa only [readAll, read, mapped_reached] using later.2.1,
            by simpa only [readAll, read, mapped_reached] using later.2.2.1, ?_⟩
          intro result after completed
          cases tail : readAll h values middle with
          | done more final =>
              have kept : Keeps middle final := by simpa only [tail, reached] using later.1
              have resident := later.2.2.2 more final tail
              simp only [readAll, read, tail, Result.bind] at completed
              cases completed
              intro edge member
              rcases List.mem_append.mp member with ownMember | restMember
              · exact InternedEdgeResidency.edge_grows middle _ kept.growth edge (own.2.2.2 edge ownMember)
              · exact resident edge restMember
          | pending key final => simp only [readAll, read, tail, Result.bind] at completed; cases completed
          | unresolved name final => simp only [readAll, read, tail, Result.bind] at completed; cases completed
          | exhausted limit final => simp only [readAll, read, tail, Result.bind] at completed; cases completed
      | pending key after =>
          rw [read] at first
          simp only [readAll, read, reached]
          exact ⟨first.keeps, first.semantic, first.costs, by intro _ _ completed; cases completed⟩
      | unresolved name after =>
          rw [read] at first
          simp only [readAll, read, reached]
          exact ⟨first.keeps, first.semantic, first.costs, by intro _ _ completed; cases completed⟩
      | exhausted after =>
          rw [read] at first
          simp only [readAll, read, reached]
          exact ⟨first.keeps, first.semantic, first.costs, by intro _ _ completed; cases completed⟩

/-- Every head outcome retains current heaps and any completed available node. -/
theorem head_effects [DecidableEq (EdgeKey Symbol Guard)] (h : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) :
    Keeps before (reached (SourceEqualityRequiredWorker.head h value before)) ∧
      SemanticReady (reached (SourceEqualityRequiredWorker.head h value before)) ∧
      CostHeap (reached (SourceEqualityRequiredWorker.head h value before)) ∧
      ∀ result after, SourceEqualityRequiredWorker.head h value before = .done result after → Available after result := by
  have first := SourceEqualityExposureCosts.nodeEdges_verified h value before semantic costs available
  cases read : MergedFreshOrdinaryExposure.nodeEdges h value before with
  | done edges middle =>
      have own := SourceEqualityProjectionCosts.read_effects (.done h read) semantic costs available
      have last := node_effects edges middle own.2.1 own.2.2.1 own.2.2.2
      simp only [SourceEqualityRequiredWorker.head, read, work, reached]
      refine ⟨own.1.trans last.1, last.2.1, last.2.2.1, ?_⟩
      intro result after completed
      cases completed
      exact last.2.2.2
  | pending key after =>
      rw [read] at first
      simp only [SourceEqualityRequiredWorker.head, read, reached]
      exact ⟨first.keeps, first.semantic, first.costs, by intro _ _ completed; cases completed⟩
  | unresolved name after =>
      rw [read] at first
      simp only [SourceEqualityRequiredWorker.head, read, reached]
      exact ⟨first.keeps, first.semantic, first.costs, by intro _ _ completed; cases completed⟩
  | exhausted after =>
      rw [read] at first
      simp only [SourceEqualityRequiredWorker.head, read, reached]
      exact ⟨first.keeps, first.semantic, first.costs, by intro _ _ completed; cases completed⟩

/-- Every union outcome retains current heaps and any completed available node. -/
theorem union_effects [DecidableEq (EdgeKey Symbol Guard)] (h : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Keeps before (reached (union h values before)) ∧ SemanticReady (reached (union h values before)) ∧
      CostHeap (reached (union h values before)) ∧
      ∀ result after, union h values before = .done result after → Available after result := by
  have first := readAll_effects h values before semantic costs available
  cases read : readAll h values before with
  | done edges middle =>
      have resident := first.2.2.2 edges middle read
      rw [read] at first
      have last := node_effects edges middle first.2.1 first.2.2.1 resident
      simp only [union, read, Result.bind, work, reached]
      refine ⟨first.1.trans last.1, last.2.1, last.2.2.1, ?_⟩
      intro result after completed
      cases completed
      exact last.2.2.2
  | pending key after =>
      rw [read] at first
      simp only [union, read, Result.bind, reached]
      exact ⟨first.1, first.2.1, first.2.2.1, by intro _ _ completed; cases completed⟩
  | unresolved name after =>
      rw [read] at first
      simp only [union, read, Result.bind, reached]
      exact ⟨first.1, first.2.1, first.2.2.1, by intro _ _ completed; cases completed⟩
  | exhausted limit after =>
      rw [read] at first
      simp only [union, read, Result.bind, reached]
      exact ⟨first.1, first.2.1, first.2.2.1, by intro _ _ completed; cases completed⟩

/-- Every ordered-read outcome derives its actual returned coherent memo. -/
theorem readAll_memos [DecidableEq (EdgeKey Symbol Guard)] (h : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, ReadAllReads h values before memo saved ∧
      Correct (reached (readAll h values before)) saved ∧ Extends memo saved := by
  induction values generalizing before memo with
  | nil => exact ⟨memo, .nil, correct, extends_refl _⟩
  | cons value values ih =>
      obtain ⟨middleMemo, calls, coherent, retained⟩ := SourceEqualityExposureMemos.nodeEdges_reads
        h value before semantic costs (available value List.mem_cons_self) memo correct
      cases read : MergedFreshOrdinaryExposure.nodeEdges h value before with
      | done edges middle =>
          have own := SourceEqualityProjectionCosts.read_effects (.done h read) semantic costs
            (available value List.mem_cons_self)
          have middleCorrect : Correct middle middleMemo := by
            simpa only [read, MergedSourceExposure.Result.state] using coherent
          obtain ⟨saved, rest, finalCorrect, finalRetained⟩ := ih middle own.2.1 own.2.2.1
            (fun child member => own.1.available child (available child (List.mem_cons_of_mem _ member)))
            middleMemo middleCorrect
          exact ⟨saved, .cons read calls rest,
            by simpa only [readAll, read, mapped_reached] using finalCorrect,
            extends_trans retained finalRetained⟩
      | pending key after =>
          exact ⟨middleMemo, .pending read calls,
            by simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using coherent, retained⟩
      | unresolved name after =>
          exact ⟨middleMemo, .unresolved read calls,
            by simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using coherent, retained⟩
      | exhausted after =>
          exact ⟨middleMemo, .exhausted read calls,
            by simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using coherent, retained⟩

/-- Every head outcome retains its exposure memo through any node construction. -/
theorem head_memos [DecidableEq (EdgeKey Symbol Guard)] (h : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, HeadReads h value before memo saved ∧
      Correct (reached (SourceEqualityRequiredWorker.head h value before)) saved ∧ Extends memo saved := by
  obtain ⟨saved, calls, coherent, retained⟩ :=
    SourceEqualityExposureMemos.nodeEdges_reads h value before semantic costs available memo correct
  refine ⟨saved, .read calls, ?_, retained⟩
  cases read : MergedFreshOrdinaryExposure.nodeEdges h value before with
  | done edges middle =>
      have own := SourceEqualityProjectionCosts.read_effects (.done h read) semantic costs available
      have middleCorrect : Correct middle saved := by
        simpa only [read, MergedSourceExposure.Result.state] using coherent
      simpa only [SourceEqualityRequiredWorker.head, read, work, reached] using
        node_correct edges middle own.2.1 own.2.2.2 saved middleCorrect
  | pending key after => simpa only [SourceEqualityRequiredWorker.head, read, reached, MergedSourceExposure.Result.state] using coherent
  | unresolved name after => simpa only [SourceEqualityRequiredWorker.head, read, reached, MergedSourceExposure.Result.state] using coherent
  | exhausted after => simpa only [SourceEqualityRequiredWorker.head, read, reached, MergedSourceExposure.Result.state] using coherent

/-- Every union outcome retains its last actual read memo through reconstruction. -/
theorem union_memos [DecidableEq (EdgeKey Symbol Guard)] (h : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, UnionReads h values before memo saved ∧
      Correct (reached (union h values before)) saved ∧ Extends memo saved := by
  obtain ⟨saved, calls, coherent, retained⟩ := readAll_memos h values before semantic costs available memo correct
  refine ⟨saved, .read calls, ?_, retained⟩
  cases read : readAll h values before with
  | done edges middle =>
      have first := readAll_effects h values before semantic costs available
      have resident := first.2.2.2 edges middle read
      rw [read] at first coherent
      simpa only [union, read, Result.bind, work, reached] using
        node_correct edges middle first.2.1 resident saved coherent
  | pending key after => simpa only [union, read, Result.bind, reached] using coherent
  | unresolved name after => simpa only [union, read, Result.bind, reached] using coherent
  | exhausted limit after => simpa only [union, read, Result.bind, reached] using coherent

end MicroCFTA.SourceEqualityProjectionOutcomePrimitives
