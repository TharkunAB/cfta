import MicroCFTA.SourceSymbolicStableIndex
import MicroCFTA.FiniteAutomatonDriver

/-!
# The symbolic callback of the finite automaton driver

The callback runs the source workers. A proved termination bound replaces
unbounded evaluation in this proof port. It does not enumerate earlier terms.
The finite reference index supplies a proof of the source workers' order.
-/
namespace MicroCFTA.SourceFiniteBackend
open Language SourceGuards SourceObservations SymbolicDriver SymbolicGraphView
open SymbolicInternedView SourceSymbolicIndex

/-- The proved stable behavior of the actual symbolic workers at one root. -/
structure Stable [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (root : Nat)
    (valid : Term Symbol → Prop) where
  index : DistinctRank.Index valid
  bound : Nat
  counted : ∀ fuel, bound ≤ fuel → cardinality graph fuel root = .ok (index.count : Int)
  selected : ∀ fuel, bound ≤ fuel → ∀ rank : Fin index.count,
    unrank graph order fuel root rank.val = .ok (index.decode rank).val
  ranked : ∀ fuel, bound ≤ fuel → ∀ term : {t // valid t},
    rankOf graph order fuel root term.val = .ok (some (index.encode term).val)
  rejected : ∀ term, ∃ extra, ∀ fuel, max bound extra ≤ fuel →
    (rankOf graph order fuel root term = .ok none ↔ ¬valid term)

variable {Symbol Order : Type} {graph : Graph Symbol} {order : Symbol → Order}
  {root : Nat} {valid : Term Symbol → Prop}

/-- The inverse worker has a finite execution bound for each submitted term. -/
noncomputable def inverseFuel [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) (term : Term Symbol) : Nat :=
  max stable.bound (Classical.choose (stable.rejected term))

/-- These callbacks execute the source workers at their proved termination bounds. -/
noncomputable def workerIndex [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) : CompactEdgeRanks.Index (Term Symbol) where
  count := stable.index.count
  select rank := if rank < stable.index.count then
    (unrank graph order stable.bound root rank).toOption else none
  rank term := ((rankOf graph order (inverseFuel stable term) root term).toOption.bind id).map Int.toNat

/-- The exposed count equals the count computed by the source worker. -/
theorem worker_count [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) :
    cardinality graph stable.bound root = .ok ((workerIndex stable).count : Int) :=
  stable.counted _ (Nat.le_refl _)

/-- The decoder calls the actual worker once for a valid rank. -/
theorem worker_select [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) (rank : Fin stable.index.count) :
    (workerIndex stable).select rank.val = some (stable.index.decode rank).val := by
  simp only [workerIndex, rank.isLt, ↓reduceIte, stable.selected _ (Nat.le_refl _) rank, Except.toOption]

/-- Accepted terms use the same stable source order in the inverse. -/
theorem worker_rank [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) (term : {t // valid t}) :
    (workerIndex stable).rank term.val = some (stable.index.encode term).val := by
  have ranked := stable.ranked (inverseFuel stable term.val) (Nat.le_max_left _ _) term
  simp only [workerIndex, ranked, Except.toOption, Option.bind_some, id_eq, Option.map_some,
    Int.toNat_natCast]

/-- Invalid terms terminate with rejection instead of a fabricated rank. -/
theorem worker_reject [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) (term : Term Symbol) (invalid : ¬valid term) :
    (workerIndex stable).rank term = none := by
  have rejected := ((Classical.choose_spec (stable.rejected term)) (inverseFuel stable term)
    (Nat.le_refl _)).mpr invalid
  simp only [workerIndex, rejected, Except.toOption, Option.bind_some, id_eq, Option.map_none]

/-- All and only valid ranks decode, without a list search in the callback. -/
theorem worker_select_iff [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) (rank : Nat) (term : Term Symbol) :
    (workerIndex stable).select rank = some term ↔
      ∃ position : Fin stable.index.count, position.val = rank ∧ (stable.index.decode position).val = term := by
  constructor
  · intro found
    have within : rank < stable.index.count := by
      by_cases within : rank < stable.index.count
      · exact within
      · simp [workerIndex, within] at found
    let position : Fin stable.index.count := ⟨rank, within⟩
    have selected := worker_select stable position
    exact ⟨position, rfl, Option.some.inj (selected.symm.trans found)⟩
  · rintro ⟨position, rfl, same⟩
    simpa only [same] using worker_select stable position

/-- The source workers satisfy the finite driver's total distinct local-index interface. -/
theorem worker_correct [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) : CompactEdgeRanks.Correct (workerIndex stable) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro rank term found
    obtain ⟨position, rfl, _⟩ := (worker_select_iff stable rank term).mp found
    exact position.isLt
  · intro rank within
    exact ⟨_, worker_select stable ⟨rank, within⟩⟩
  · intro rank term
    by_cases accepted : valid term
    · let member : {t // valid t} := ⟨term, accepted⟩
      rw [worker_rank stable member]
      constructor
      · intro same
        have sameRank := Option.some.inj same
        have selected := worker_select stable (stable.index.encode member)
        rw [DistinctRank.Index.decode_encode, sameRank] at selected
        exact selected
      · intro found
        obtain ⟨position, sameRank, sameTerm⟩ := (worker_select_iff stable rank term).mp found
        have same : stable.index.decode position = member := Subtype.ext sameTerm
        have ranks := congrArg stable.index.encode same
        rw [DistinctRank.Index.encode_decode] at ranks
        exact congrArg some ((congrArg Fin.val ranks).symm.trans sameRank)
    · rw [worker_reject stable term accepted]
      constructor
      · intro impossible; cases impossible
      · intro found
        obtain ⟨position, _, same⟩ := (worker_select_iff stable rank term).mp found
        exact False.elim (accepted (same ▸ (stable.index.decode position).property))

/-- The callback's output domain is the independent guarded graph language. -/
theorem worker_language [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) (term : Term Symbol) :
    (∃ rank, (workerIndex stable).select rank = some term) ↔ valid term := by
  constructor
  · rintro ⟨rank, found⟩
    obtain ⟨position, _, same⟩ := (worker_select_iff stable rank term).mp found
    exact same ▸ (stable.index.decode position).property
  · intro accepted
    let member : {t // valid t} := ⟨term, accepted⟩
    refine ⟨(stable.index.encode member).val, ?_⟩
    simpa only [DistinctRank.Index.decode_encode] using worker_select stable (stable.index.encode member)

/-- Source symbolicRanked rejects exactly zero cardinality before returning its callbacks. -/
noncomputable def compile [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) : Except Unit (CompactEdgeRanks.Index (Term Symbol)) :=
  if (workerIndex stable).count = 0 then .error () else .ok (workerIndex stable)

/-- Both the empty and successful symbolic branches satisfy the finite driver. -/
theorem compile_exact [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (stable : Stable graph order root valid) :
    FiniteAutomatonDriver.ResultExact valid (compile stable).toOption := by
  classical
  unfold compile
  split
  · rename_i empty
    intro term accepted
    obtain ⟨rank, selected⟩ := (worker_language stable term).mpr accepted
    have within := (worker_correct stable).bounded rank term selected
    omega
  · rename_i nonempty
    exact ⟨by omega, worker_correct stable, worker_language stable⟩

/-- Actual source compilation, allocated rows, and operation readback derive the callback certificate. -/
theorem source_stable [DecidableEq Formula] [Ord (Label Formula)] [Ord Order] [DecidableEq Payload]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (shape : Payload → List (Language.Edge Nat (Label Formula)))
    (graph : Graph (Label Formula)) (order : Label Formula → Order)
    (constraints : SymbolicDriver.Edge (Label Formula) → Constraint Formula)
    (compiled : CompiledRows graph constraints)
    (view : ClosedOperationRows graph (fun edge => acceptsConstraint formulas solver (constraints edge)))
    (allocated : AllocatedRows shape (automaton graph (fun edge => acceptsConstraint formulas solver (constraints edge))))
    (fallback : Term (Label Formula)) (root : Nat) :
    Nonempty (Stable graph order root
      (Accepts (automaton graph (fun edge => acceptsConstraint formulas solver (constraints edge))) root)) := by
  obtain ⟨index, bound, running, rejected⟩ :=
    SourceSymbolicStableIndex.stable_source_index formulas solver shape graph order constraints compiled view allocated fallback root
  exact ⟨⟨index, bound, fun fuel enough => (running fuel enough).1,
    fun fuel enough => (running fuel enough).2.1, fun fuel enough => (running fuel enough).2.2, rejected⟩⟩

end MicroCFTA.SourceFiniteBackend
