import MicroCFTA.SourceSizedDeterminizationHolderOrder

/-!
# Finite set views for discovery control

Known lists can have different orders. Membership determines freshness,
emptiness, and the next ordered batch. Distinct known lists also have
the same cardinality. These laws do not equate native holder lists or
assume a common arity for all rows of a symbol.
-/
namespace MicroCFTA.SourceSizedDeterminizationSetView
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationFrontier Std
attribute [local instance] lexOrd

/-- Equal known membership gives the same fresh list for a fixed found list. -/
theorem fresh_eq {Key : Type} [DecidableEq Key] (first second found : List Key)
    (same : ∀ key, key ∈ first ↔ key ∈ second) :
    SourceSizedDeterminizationDiscovery.fresh first found =
      SourceSizedDeterminizationDiscovery.fresh second found := by
  unfold SourceSizedDeterminizationDiscovery.fresh
  apply List.filter_congr
  intro key _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr (same key)

/-- Adding the fresh keys preserves distinctness without a distinct found list. -/
theorem more_nodup {Key : Type} [DecidableEq Key] (known found : List Key)
    (distinct : known.Nodup) :
    (known ++ SourceSizedDeterminizationDiscovery.fresh known found).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨distinct, ?_, ?_⟩
  · exact (SymbolicDriver.eraseDups_nodup found).filter _
  · intro previous older current recent equal
    have excluded : current ∉ known := of_decide_eq_true (List.mem_filter.mp recent).2
    exact excluded (equal ▸ older)

/-- Equal membership detects the same empty list. -/
theorem empty_iff {Key : Type} (first second : List Key)
    (same : ∀ key, key ∈ first ↔ key ∈ second) : first = [] ↔ second = [] := by
  simp only [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro absent key present
    exact absent key ((same key).mpr present)
  · intro absent key present
    exact absent key ((same key).mp present)

/-- Distinct lists with equal membership have equal cardinality. -/
theorem length_eq {Key : Type} (first second : List Key)
    (same : ∀ key, key ∈ first ↔ key ∈ second)
    (firstDistinct : first.Nodup) (secondDistinct : second.Nodup) :
    first.length = second.length :=
  ((List.perm_ext_iff_of_nodup firstDistinct secondDistinct).mpr same).length_eq

/-- Tuple membership uses known membership only to detect the initial leaf case. -/
theorem mem_tuples_congr {State Key : Type} [DecidableEq Key]
    (fresh : List Key) (first second : State → List Key) (before after : List Key)
    (holders : ∀ state key, key ∈ first state ↔ key ∈ second state)
    (known : ∀ key, key ∈ before ↔ key ∈ after)
    (states : List State) (keys : List Key) :
    keys ∈ tuples fresh first before states ↔ keys ∈ tuples fresh second after states := by
  have empty := empty_iff before after known
  constructor
  · intro member
    obtain ⟨related, active⟩ := (mem_tuples fresh first before states keys).mp member
    refine (mem_tuples fresh second after states keys).mpr
      ⟨related.imp (fun state key included => (holders state key).mp included), ?_⟩
    rcases active with leaf | recent
    · exact Or.inl ⟨leaf.1, empty.mp leaf.2⟩
    · exact Or.inr recent
  · intro member
    obtain ⟨related, active⟩ := (mem_tuples fresh second after states keys).mp member
    refine (mem_tuples fresh first before states keys).mpr
      ⟨related.imp (fun state key included => (holders state key).mpr included), ?_⟩
    rcases active with leaf | recent
    · exact Or.inl ⟨leaf.1, empty.mpr leaf.2⟩
    · exact Or.inr recent

section Ordered
variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
  [Ord State] [TransOrd State] [LawfulEqOrd State]

/-- Canonical tuple readback ignores holder order and known discovery order. -/
theorem tupleSet_eq (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (first second : State → List (List State))
    (before after : List (List State))
    (holders : ∀ state key, key ∈ first state ↔ key ∈ second state)
    (known : ∀ key, key ∈ before ↔ key ∈ after) (wanted : Symbol × Nat) :
    SourceSizedDeterminizationOrderedStep.tupleSet states rows fresh first before wanted =
      SourceSizedDeterminizationOrderedStep.tupleSet states rows fresh second after wanted := by
  unfold SourceSizedDeterminizationOrderedStep.tupleSet
  apply CanonicalClasses.sortedSet_ext
  intro keys
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨seed, present, generated⟩
    exact ⟨seed, present,
      (mem_tuples_congr fresh first second before after holders known seed keys).mp generated⟩
  · rintro ⟨seed, present, generated⟩
    exact ⟨seed, present,
      (mem_tuples_congr fresh first second before after holders known seed keys).mpr generated⟩

/-- The complete ordered round depends on the two set views through membership. -/
theorem round_eq [Ord Symbol] (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (first second : State → List (List State))
    (before after : List (List State))
    (holders : ∀ state key, key ∈ first state ↔ key ∈ second state)
    (known : ∀ key, key ∈ before ↔ key ∈ after) :
    SourceSizedDeterminizationOrderedStep.round states rows fresh first before =
      SourceSizedDeterminizationOrderedStep.round states rows fresh second after := by
  unfold SourceSizedDeterminizationOrderedStep.round
  apply congrArg (fun generate : (Symbol × Nat) → List (Choice State Symbol) =>
    (SourceSizedDeterminizationOrderedStep.tokens states rows).flatMap generate)
  funext wanted
  rw [tupleSet_eq states rows fresh first second before after holders known wanted]

end Ordered
end MicroCFTA.SourceSizedDeterminizationSetView
