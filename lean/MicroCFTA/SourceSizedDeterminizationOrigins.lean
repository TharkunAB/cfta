import MicroCFTA.SourceSizedDeterminizationRun

/-!
# Exact origins of discovered subset keys

Every known or pending key is a target of an accumulated emitted choice.
Each step retains those choices and appends the next batch. A successful
compile therefore discovers exactly the target keys of its returned table.
This is a membership law. It does not identify map iteration order.
-/
namespace MicroCFTA.SourceSizedDeterminizationOrigins
open Language SourceSizedDeterminizationKernel
open SourceSizedDeterminizationDiscovery SourceSizedDeterminizationRun

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

private theorem advance_origins (states : List State) (rows : Automaton State Symbol)
    (known found : List (List State)) (choices : List (Choice State Symbol))
    (previous : ∀ key ∈ known,
      ∃ choice ∈ choices, target states rows choice.1 choice.2 = key)
    (current : ∀ key ∈ found,
      ∃ choice ∈ choices, target states rows choice.1 choice.2 = key) :
    (∀ key ∈ known ++ fresh known found,
      ∃ choice ∈ (step states rows (fresh known found) (known ++ fresh known found) choices).2,
        target states rows choice.1 choice.2 = key) ∧
    (∀ key ∈ (step states rows (fresh known found) (known ++ fresh known found) choices).1,
      ∃ choice ∈ (step states rows (fresh known found) (known ++ fresh known found) choices).2,
        target states rows choice.1 choice.2 = key) := by
  constructor
  · intro key member
    have witness := (List.mem_append.mp member).elim (previous key)
      (fun recent => current key ((mem_fresh known found key).mp recent).1)
    obtain ⟨choice, present, same⟩ := witness
    exact ⟨choice, List.mem_append.mpr (Or.inl present), same⟩
  · intro key member
    obtain ⟨choice, present, same⟩ := List.mem_map.mp member
    exact ⟨choice, List.mem_append.mpr (Or.inr present), same⟩

private theorem evaluation_origins (limit : Nat) (states : List State)
    (rows : Automaton State Symbol) (known found : List (List State))
    (choices : List (Choice State Symbol)) (calls : Nat)
    (result : Outcome (List State) (List (Choice State Symbol)))
    (execution : Evaluation limit (step states rows) known found choices calls result)
    (finalKnown : List (List State)) (finalChoices : List (Choice State Symbol))
    (returned : result = .ready finalKnown finalChoices)
    (previous : ∀ key ∈ known,
      ∃ choice ∈ choices, target states rows choice.1 choice.2 = key)
    (current : ∀ key ∈ found,
      ∃ choice ∈ choices, target states rows choice.1 choice.2 = key) :
    ∀ key ∈ finalKnown,
      ∃ choice ∈ finalChoices, target states rows choice.1 choice.2 = key := by
  revert previous current
  induction execution with
  | limit_exceeded => cases returned
  | done within empty =>
      intro previous current
      cases returned
      intro key member
      exact previous key (by simpa only [empty, List.append_nil] using member)
  | next within nonempty following ih =>
      intro previous current
      have next := advance_origins states rows _ _ _ previous current
      exact ih returned next.1 next.2

/-- Actual successful discovery returns exactly the targets of its accumulated choices. -/
theorem compile_key_origin (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) (key : List State) :
    key ∈ known ↔ ∃ choice ∈ choices, target states rows choice.1 choice.2 = key := by
  constructor
  · obtain ⟨calls, _, execution, _⟩ := compile_complete limit states rows
    have origins := evaluation_origins limit states rows [] _ _ calls _ execution known choices returned
      (by intro key impossible; cases impossible)
      (by intro key member; exact List.mem_map.mp member)
    exact origins key
  · rintro ⟨choice, member, same⟩
    have closed := compile_closed limit states rows known choices returned
    rcases closed.targets choice member with present | impossible
    · exact same ▸ present
    · cases impossible

/-- Returned known keys and accumulated table targets have identical membership. -/
theorem compile_targets_exact (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) (key : List State) :
    key ∈ known ↔ key ∈ targets states rows choices := by
  simpa only [targets, List.mem_map] using
    compile_key_origin limit states rows known choices returned key

/-- Every returned key retains the original state inventory's relative order. -/
theorem compile_key_sublist (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices)
    (key : List State) (member : key ∈ known) : key.Sublist states := by
  obtain ⟨choice, _, same⟩ := (compile_key_origin limit states rows known choices returned key).mp member
  rw [← same]
  exact List.filter_sublist

/-- Distinct original map keys give distinct members within each discovered key. -/
theorem compile_key_nodup (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) (distinct : states.Nodup)
    (key : List State) (member : key ∈ known) : key.Nodup :=
  (compile_key_sublist limit states rows known choices returned key member).nodup distinct

end MicroCFTA.SourceSizedDeterminizationOrigins
