import MicroCFTA.SourceSizedDeterminizationOrderedRun

/-!
# Holder membership determines ordered batches

The native holder update appends a fresh bucket. Its `fromListWith (<>)`
schedule reverses the singleton insertion order within that bucket.
The recomputed holder list can have a different order. The tuple set
removes this difference before the ordered round emits its choices.

The update below models each state's singleton insertion schedule.
Its attachment to native set readback still requires that each set
enumerates its states once. No container representation law is assumed
by the tuple or round congruence theorems.
-/
namespace MicroCFTA.SourceSizedDeterminizationHolderOrder
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationFrontier Std
attribute [local instance] lexOrd

/-- Tuple membership depends on holder membership, including the initial leaf case. -/
theorem mem_tuples_congr {State Key : Type} [DecidableEq Key]
    (fresh : List Key) (first second : State → List Key) (known : List Key)
    (same : ∀ state key, key ∈ first state ↔ key ∈ second state)
    (states : List State) (keys : List Key) :
    keys ∈ tuples fresh first known states ↔ keys ∈ tuples fresh second known states := by
  constructor
  · intro member
    obtain ⟨related, active⟩ := (mem_tuples fresh first known states keys).mp member
    exact (mem_tuples fresh second known states keys).mpr
      ⟨related.imp (fun state key included => (same state key).mp included), active⟩
  · intro member
    obtain ⟨related, active⟩ := (mem_tuples fresh second known states keys).mp member
    exact (mem_tuples fresh first known states keys).mpr
      ⟨related.imp (fun state key included => (same state key).mpr included), active⟩

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
  [Ord State] [TransOrd State] [LawfulEqOrd State]

/-- Canonical tuple-set readback removes every holder-order difference. -/
theorem tupleSet_eq (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (first second : State → List (List State))
    (known : List (List State))
    (same : ∀ state key, key ∈ first state ↔ key ∈ second state)
    (wanted : Symbol × Nat) :
    SourceSizedDeterminizationOrderedStep.tupleSet states rows fresh first known wanted =
      SourceSizedDeterminizationOrderedStep.tupleSet states rows fresh second known wanted := by
  unfold SourceSizedDeterminizationOrderedStep.tupleSet
  apply CanonicalClasses.sortedSet_ext
  intro keys
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨seed, present, generated⟩
    exact ⟨seed, present, (mem_tuples_congr fresh first second known same seed keys).mp generated⟩
  · rintro ⟨seed, present, generated⟩
    exact ⟨seed, present, (mem_tuples_congr fresh first second known same seed keys).mpr generated⟩

/-- The complete ordered choice sequence depends only on holder membership. -/
theorem round_eq [Ord Symbol] (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (first second : State → List (List State))
    (known : List (List State))
    (same : ∀ state key, key ∈ first state ↔ key ∈ second state) :
    SourceSizedDeterminizationOrderedStep.round states rows fresh first known =
      SourceSizedDeterminizationOrderedStep.round states rows fresh second known := by
  unfold SourceSizedDeterminizationOrderedStep.round
  apply congrArg (fun generate : (Symbol × Nat) → List (Choice State Symbol) =>
    (SourceSizedDeterminizationOrderedStep.tokens states rows).flatMap generate)
  funext wanted
  rw [tupleSet_eq states rows fresh first second known same wanted]

/-- Append the per-state fresh bucket in native singleton insertion order. -/
def sourceUpdate (holding : State → List (List State)) (fresh : List (List State))
    (state : State) : List (List State) :=
  holding state ++ (fresh.filter fun key => decide (state ∈ key)).reverse

omit [Ord State] [TransOrd State] [LawfulEqOrd State] in
/-- The native-style update and recomputed holders retain exactly the same membership. -/
theorem sourceUpdate_membership (holding : State → List (List State))
    (known fresh : List (List State))
    (same : ∀ state key,
      key ∈ holding state ↔ key ∈ SourceSizedDeterminizationRun.holders known state)
    (state : State) (key : List State) :
    key ∈ sourceUpdate holding fresh state ↔
      key ∈ SourceSizedDeterminizationRun.holders (known ++ fresh) state := by
  simp only [sourceUpdate, List.mem_append, List.mem_reverse, List.mem_filter,
    decide_eq_true_eq, same state key, SourceSizedDeterminizationRun.mem_holders]
  constructor
  · rintro (⟨present, contains⟩ | ⟨present, contains⟩)
    · exact ⟨Or.inl present, contains⟩
    · exact ⟨Or.inr present, contains⟩
  · rintro ⟨present | present, contains⟩
    · exact Or.inl ⟨present, contains⟩
    · exact Or.inr ⟨present, contains⟩

end MicroCFTA.SourceSizedDeterminizationHolderOrder
