import MicroCFTA.SourceSizedDeterminizationSetView
import MicroCFTA.SourceSizedDeterminizationHolderInsertion
import MicroCFTA.SourceSizedDeterminizationOrderedOrigins

/-!
# Determinization with source set and holder updates

The known set uses ascending, distinct readback. Each round inserts the
fresh singleton holder entries in the source order. The accumulated table
and the current found batch remain separate until the next limit check.
Their concatenation represents old buckets followed by new buckets.

The proof derives correspondence with ordered discovery from empty maps.
It supplies no caller invariant, output carrier, or recursion bound.
These are set and map value views. Native storage, machine integers, and
total work inside each round require separate correspondence proofs.
-/
namespace MicroCFTA.SourceSizedDeterminizationSourceLoop
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationClosure
open SourceSizedDeterminizationDiscovery Std
attribute [local instance] lexOrd

variable {State : Type} [DecidableEq State] [Ord State] [TransOrd State] [LawfulEqOrd State]

/-- Read a completed known set in ascending order. Preserve both failure outcomes. -/
def normalize {Symbol : Type} :
    Outcome (List State) (List (Choice State Symbol)) →
      Outcome (List State) (List (Choice State Symbol))
  | .limitExceeded => .limitExceeded
  | .ready known choices => .ready (CanonicalClasses.sortedSet known) choices
  | .exhausted => .exhausted

private theorem more_eq (first second found : List (List State))
    (same : ∀ key, key ∈ first ↔ key ∈ second) :
    CanonicalClasses.sortedSet (first ++ fresh first found) =
      CanonicalClasses.sortedSet (second ++ fresh second found) := by
  rw [SourceSizedDeterminizationSetView.fresh_eq first second found same]
  apply CanonicalClasses.sortedSet_ext
  intro key
  simp only [List.mem_append]
  exact or_congr (same key) Iff.rfl

private theorem more_size (first second found : List (List State))
    (same : ∀ key, key ∈ first ↔ key ∈ second) (distinct : second.Nodup) :
    (CanonicalClasses.sortedSet (first ++ fresh first found)).length =
      (second ++ fresh second found).length := by
  rw [more_eq first second found same]
  exact SourceSizedDeterminizationSetView.length_eq _ _
    (CanonicalClasses.mem_sortedSet _) (CanonicalClasses.sortedSet_nodup _)
    (SourceSizedDeterminizationSetView.more_nodup second found distinct)

variable {Symbol : Type} [DecidableEq Symbol] [Ord Symbol]

/-- Merge the current batch, check the set cardinality, then update holders and continue. -/
def go (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    Nat → List (List State) → (State → List (List State)) →
      List (Choice State Symbol) → List (Choice State Symbol) →
        Outcome (List State) (List (Choice State Symbol))
  | fuel, known, holding, table, found =>
    let new := fresh known (SourceSizedDeterminizationOrderedRun.foundKeys states rows found)
    let more := CanonicalClasses.sortedSet (known ++ new)
    let combined := table ++ found
    if limit < more.length then .limitExceeded
    else if new = [] then .ready more combined
    else match fuel with
      | 0 => .exhausted
      | remaining + 1 =>
        let updated := SourceSizedDeterminizationHolderInsertion.update holding new
        let batch := SourceSizedDeterminizationOrderedStep.round states rows new updated more
        go limit states rows remaining more updated combined batch

private theorem next_round_eq (states : List State) (rows : Automaton State Symbol)
    (new first second : List (List State)) (holding : State → List (List State))
    (same : ∀ key, key ∈ first ↔ key ∈ second)
    (holders : ∀ state key,
      key ∈ holding state ↔ key ∈ SourceSizedDeterminizationRun.holders second state) :
    SourceSizedDeterminizationOrderedStep.round states rows new
        (SourceSizedDeterminizationHolderInsertion.update holding new)
        (CanonicalClasses.sortedSet (first ++ new)) =
      SourceSizedDeterminizationOrderedStep.round states rows new
        (SourceSizedDeterminizationRun.holders (second ++ new)) (second ++ new) := by
  apply SourceSizedDeterminizationSetView.round_eq
  · exact SourceSizedDeterminizationHolderInsertion.update_membership holding second new holders
  · intro key
    rw [CanonicalClasses.mem_sortedSet]
    simp only [List.mem_append]
    exact or_congr (same key) Iff.rfl

/-- Every bounded source loop has exactly the ordered controller's result and table. -/
theorem go_refines (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (fuel : Nat) (first second : List (List State)) (holding : State → List (List State))
    (table found : List (Choice State Symbol)) (distinct : second.Nodup)
    (same : ∀ key, key ∈ first ↔ key ∈ second)
    (holders : ∀ state key,
      key ∈ holding state ↔ key ∈ SourceSizedDeterminizationRun.holders second state) :
    go limit states rows fuel first holding table found =
      normalize (run limit (SourceSizedDeterminizationOrderedRun.step states rows) fuel second
        (SourceSizedDeterminizationOrderedRun.foundKeys states rows found) (table ++ found)) := by
  induction fuel generalizing first second holding table found with
  | zero =>
    have sameFresh := SourceSizedDeterminizationSetView.fresh_eq first second
      (SourceSizedDeterminizationOrderedRun.foundKeys states rows found) same
    have size := more_size first second
      (SourceSizedDeterminizationOrderedRun.foundKeys states rows found) same distinct
    have more := more_eq first second
      (SourceSizedDeterminizationOrderedRun.foundKeys states rows found) same
    rw [sameFresh] at size more
    rw [go, run, sameFresh, size]
    by_cases over : limit < (second ++ fresh second
      (SourceSizedDeterminizationOrderedRun.foundKeys states rows found)).length
    · rw [ite_eq_left over, ite_eq_left over]
      rfl
    · rw [ite_eq_right over, ite_eq_right over]
      by_cases empty : fresh second
        (SourceSizedDeterminizationOrderedRun.foundKeys states rows found) = []
      · rw [ite_eq_left empty, ite_eq_left empty]
        exact congrArg (fun known => Outcome.ready known (table ++ found)) more
      · rw [ite_eq_right empty, ite_eq_right empty]
        rfl
  | succ remaining ih =>
    let pending := SourceSizedDeterminizationOrderedRun.foundKeys states rows found
    let new := fresh second pending
    have sameFresh := SourceSizedDeterminizationSetView.fresh_eq first second pending same
    have size := more_size first second pending same distinct
    have more := more_eq first second pending same
    rw [sameFresh] at size more
    rw [go, run, sameFresh, size]
    by_cases over : limit < (second ++ new).length
    · rw [ite_eq_left over, ite_eq_left over]
      rfl
    · rw [ite_eq_right over, ite_eq_right over]
      by_cases empty : new = []
      · rw [ite_eq_left empty, ite_eq_left empty]
        exact congrArg (fun known => Outcome.ready known (table ++ found)) more
      · rw [ite_eq_right empty, ite_eq_right empty]
        dsimp only
        have batch := next_round_eq states rows new first second holding same holders
        rw [batch]
        apply ih
        · exact SourceSizedDeterminizationSetView.more_nodup second pending distinct
        · intro key
          rw [CanonicalClasses.mem_sortedSet]
          simp only [List.mem_append]
          exact or_congr (same key) Iff.rfl
        · exact SourceSizedDeterminizationHolderInsertion.update_membership holding second new holders

/-- Start the source loop with empty known, holder, and accumulated maps. -/
def compile (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    Outcome (List State) (List (Choice State Symbol)) :=
  go limit states rows limit [] (fun _ => []) []
    (SourceSizedDeterminizationOrderedRun.initial states rows)

/-- Source set and incremental holder execution derives the same complete ordered table. -/
theorem compile_eq (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    compile limit states rows = normalize (SourceSizedDeterminizationOrderedRun.compile limit states rows) := by
  exact go_refines limit states rows limit [] [] (fun _ => []) [] _ List.nodup_nil
    (fun _ => Iff.rfl) (by intro state key; simp [SourceSizedDeterminizationRun.holders])

/-- The original limit supplies enough recursion for the source set and holder loop. -/
theorem compile_terminal (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    compile limit states rows ≠ .exhausted := by
  have terminal := (SourceSizedDeterminizationOrderedRun.compile_complete limit states rows).choose_spec.2.2
  rw [compile_eq]
  cases result : SourceSizedDeterminizationOrderedRun.compile limit states rows with
  | limitExceeded => simp [normalize]
  | ready known choices => simp [normalize]
  | exhausted => exact False.elim (terminal result)

/-- A returned source table has a derived ordered-discovery origin. -/
theorem compile_ready (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) :
    ∃ before, SourceSizedDeterminizationOrderedRun.compile limit states rows = .ready before choices ∧
      known = CanonicalClasses.sortedSet before := by
  rw [compile_eq] at returned
  cases result : SourceSizedDeterminizationOrderedRun.compile limit states rows with
  | limitExceeded => simp [result, normalize] at returned
  | exhausted => simp [result, normalize] at returned
  | ready before accumulated =>
    rw [result] at returned
    change Outcome.ready (CanonicalClasses.sortedSet before) accumulated = .ready known choices at returned
    cases returned
    exact ⟨before, rfl, rfl⟩

/-- Successful source execution supplies all closure and distinctness conditions. -/
theorem compile_closed (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) : Closed states rows known choices := by
  obtain ⟨before, origin, rfl⟩ := compile_ready limit states rows known choices returned
  have closed := SourceSizedDeterminizationOrderedRun.compile_closed limit states rows before choices origin
  refine ⟨?_, ?_, ?_, closed.distinct, CanonicalClasses.sortedSet_nodup before⟩
  · intro state present edge stored keys related
    exact closed.covered state present edge stored keys
      (related.imp (fun _ key facts => ⟨(CanonicalClasses.mem_sortedSet before key).mp facts.1, facts.2⟩))
  · intro choice present key child
    exact (CanonicalClasses.mem_sortedSet before key).mpr (closed.children choice present key child)
  · intro choice present
    exact (closed.targets choice present).imp
      (fun member => (CanonicalClasses.mem_sortedSet before _).mpr member) id

/-- Returned source set keys are exactly the emitted table targets. -/
theorem compile_targets_exact (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) (key : List State) :
    key ∈ known ↔ key ∈ SourceSizedDeterminizationRun.targets states rows choices := by
  obtain ⟨before, origin, rfl⟩ := compile_ready limit states rows known choices returned
  exact (CanonicalClasses.mem_sortedSet before key).trans
    (SourceSizedDeterminizationOrderedOrigins.compile_targets_exact limit states rows before choices origin key)

/-- The source loop retains the exact original language at every Left state. -/
theorem compile_language (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows) (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) (state : State) (term : Term Symbol) :
    Accepts (SourceSizedDeterminizationRows.rows states rows choices) (.inl state) term ↔
      Accepts rows state term :=
  SourceSizedDeterminizationRows.left_accepts_iff states rows plain supported known choices
    (compile_closed limit states rows known choices returned) state term

/-- The source loop returns unique size classes on the full Left/Right graph. -/
theorem compile_unique (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows) (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) :
    SizedRank.Unambiguous (SourceSizedDeterminizationRows.rows states rows choices) :=
  SourceSizedDeterminizationRows.classes_unique states rows plain supported choices
    (compile_closed limit states rows known choices returned).distinct

end MicroCFTA.SourceSizedDeterminizationSourceLoop
