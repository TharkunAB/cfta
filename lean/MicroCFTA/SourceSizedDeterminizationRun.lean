import MicroCFTA.SourceSizedDeterminizationClosure
import MicroCFTA.SourceSizedDeterminizationDiscovery
import MicroCFTA.SourceSizedDeterminizationStep

/-!
# Complete bounded subset discovery

The source is `Gen.Internal.Table.deterministicRows`. This finite list view
instantiates the discovery controller with the actual token/tuple round.
The context includes the accumulated choices AND the current found batch.
Thus the final batch survives when all its target keys are already known.
This corresponds to merging `table` and `found` before the source returns.

Successful discovery derives closed rows and distinct choices. It requires
no supplied coverage, closure, uniqueness, or completed worker witness.
The model retains set membership. Ordered map/set readback, the final row
sort, Left/Right state wrapping, and total tuple work remain separate.
-/
namespace MicroCFTA.SourceSizedDeterminizationRun
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationFrontier
open SourceSizedDeterminizationStep SourceSizedDeterminizationDiscovery
open SourceSizedDeterminizationClosure

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

/-- Read the discovered subsets that contain an original child state. -/
def holders (known : List (List State)) (state : State) : List (List State) :=
  known.filter fun key => decide (state ∈ key)

/-- Holder membership retains both discovery and original-state membership. -/
theorem mem_holders (known : List (List State)) (state : State) (key : List State) :
    key ∈ holders known state ↔ key ∈ known ∧ state ∈ key := by
  simp only [holders, List.mem_filter, decide_eq_true_eq]

/-- The found map's keys are the targets of the current emitted batch. -/
def targets (states : List State) (rows : Automaton State Symbol)
    (choices : List (Choice State Symbol)) : List (List State) :=
  choices.map fun choice => target states rows choice.1 choice.2

/-- Initial discovery emits all leaf choices and has no known child key. -/
def initial (states : List State) (rows : Automaton State Symbol) : List (Choice State Symbol) :=
  round states rows [] (holders []) []

/-- Add the next batch before its target keys become the next pending keys. -/
def step (states : List State) (rows : Automaton State Symbol)
    (new known : List (List State)) (choices : List (Choice State Symbol)) :
    List (List State) × List (Choice State Symbol) :=
  let batch := round states rows new (holders known) known
  (targets states rows batch, choices ++ batch)

/-- The source limit computes the complete discovery recursion bound. -/
def compile (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    Outcome (List State) (List (Choice State Symbol)) :=
  run limit (step states rows) limit [] (targets states rows (initial states rows)) (initial states rows)

private theorem all₂_right {A B : Type} {relation : A → B → Prop}
    {as : List A} {bs : List B} (related : All₂ relation as bs) (b : B) (member : b ∈ bs) :
    ∃ a, relation a b := by
  induction related with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨_, head⟩
      · exact ih tail

private theorem all₂_markRight {A B : Type} {relation : A → B → Prop}
    {as : List A} {bs : List B} (related : All₂ relation as bs) :
    All₂ (fun a b => b ∈ bs ∧ relation a b) as bs := by
  induction related with
  | nil => exact .nil
  | cons head rest ih =>
      exact .cons ⟨by simp, head⟩ (ih.imp (fun _ _ facts => ⟨List.mem_cons_of_mem _ facts.1, facts.2⟩))

/-- Fresh targets are precisely the found keys absent from the earlier known set. -/
theorem mem_fresh (known found : List (List State)) (key : List State) :
    key ∈ fresh known found ↔ key ∈ found ∧ key ∉ known := by
  simp only [fresh, List.mem_filter, List.mem_eraseDups, decide_eq_true_eq]

private theorem fresh_distinct {Key : Type} [DecidableEq Key] (known found : List Key) :
    (fresh known found).Nodup := by
  unfold fresh
  exact (SymbolicDriver.eraseDups_nodup found).filter _

private theorem found_in_more (known found : List (List State)) (key : List State)
    (member : key ∈ found) : key ∈ known ++ fresh known found := by
  by_cases old : key ∈ known
  · exact List.mem_append.mpr (Or.inl old)
  · exact List.mem_append.mpr (Or.inr ((mem_fresh known found key).mpr ⟨member, old⟩))

private theorem batch_children (states : List State) (rows : Automaton State Symbol)
    (new known : List (List State)) (choice : Choice State Symbol)
    (member : choice ∈ round states rows new (holders known) known)
    (key : List State) (child : key ∈ choice.2) : key ∈ known := by
  obtain ⟨_, _, edge, _, _, generated⟩ := (mem_round states rows new (holders known) known choice).mp member
  have paired := ((mem_tuples new (holders known) known edge.children choice.2).mp generated).1
  obtain ⟨_, present⟩ := all₂_right paired key child
  exact (mem_holders known _ key).mp present |>.1

/-- The initial leaf batch establishes every discovery invariant from empty known keys. -/
theorem initial_invariant (states : List State) (rows : Automaton State Symbol) :
    Invariant states rows [] (targets states rows (initial states rows)) (initial states rows) := by
  refine ⟨?_, ?_, ?_, round_distinct states rows [] (holders []) [], List.nodup_nil⟩
  · intro state present edge stored keys related
    have emptyKeys : keys = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro key member
      obtain ⟨_, impossible⟩ := all₂_right related key member
      cases impossible.1)
    have emptyChildren : edge.children = [] := List.length_eq_zero_iff.mp (by
      rw [related.length_eq, emptyKeys]
      rfl)
    subst keys
    apply (mem_round states rows [] (holders []) [] (edge.label, [])).mpr
    refine ⟨state, present, edge, stored, rfl, ?_⟩
    rw [emptyChildren]
    exact (mem_tuples [] (holders []) [] [] []).mpr ⟨.nil, Or.inl ⟨rfl, rfl⟩⟩
  · intro choice member key child
    exact batch_children states rows [] [] choice member key child
  · intro choice member
    exact Or.inr (List.mem_map.mpr ⟨choice, member, rfl⟩)

/-- A continuing source round retains coverage, pending targets, and distinct choices. -/
theorem advance (states : List State) (rows : Automaton State Symbol)
    (known found : List (List State)) (choices : List (Choice State Symbol))
    (invariant : Invariant states rows known found choices)
    (nonempty : fresh known found ≠ []) :
    Invariant states rows (known ++ fresh known found)
      (step states rows (fresh known found) (known ++ fresh known found) choices).1
      (step states rows (fresh known found) (known ++ fresh known found) choices).2 := by
  let new := fresh known found
  let more := known ++ new
  let batch := round states rows new (holders more) more
  change Invariant states rows more (targets states rows batch) (choices ++ batch)
  have started : more ≠ [] := fun empty => nonempty (List.append_eq_nil_iff.mp empty).2
  have disjoint : ∀ key ∈ known, key ∉ new := by
    intro key old recent
    exact ((mem_fresh known found key).mp recent).2 old
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · classical
    intro state present edge stored keys related
    by_cases recent : ∃ key ∈ keys, key ∈ new
    · apply List.mem_append.mpr
      apply Or.inr
      apply (mem_round states rows new (holders more) more (edge.label, keys)).mpr
      refine ⟨state, present, edge, stored, rfl, ?_⟩
      apply (mem_tuples new (holders more) more edge.children keys).mpr
      exact ⟨related.imp (fun child key facts => (mem_holders more child key).mpr facts), Or.inr recent⟩
    · have older : All₂ (fun child key => key ∈ known ∧ child ∈ key) edge.children keys :=
        (all₂_markRight related).imp (by
          intro child key facts
          refine ⟨?_, facts.2.2⟩
          rcases List.mem_append.mp facts.2.1 with old | freshKey
          · exact old
          · exact False.elim (recent ⟨key, facts.1, freshKey⟩))
      exact List.mem_append.mpr (Or.inl (invariant.covered state present edge stored keys older))
  · intro choice member key child
    rcases List.mem_append.mp member with previous | current
    · exact List.mem_append.mpr (Or.inl (invariant.children choice previous key child))
    · exact batch_children states rows new more choice current key child
  · intro choice member
    rcases List.mem_append.mp member with previous | current
    · apply Or.inl
      rcases invariant.targets choice previous with old | pending
      · exact List.mem_append.mpr (Or.inl old)
      · exact found_in_more known found _ pending
    · exact Or.inr (List.mem_map.mpr ⟨choice, current, rfl⟩)
  · apply List.pairwise_append.mpr
    refine ⟨invariant.distinct, round_distinct states rows new (holders more) more, ?_⟩
    intro previous stored current generated same
    subst current
    apply round_old_excluded states rows new (holders more) more started previous
    · intro key child
      exact disjoint key (invariant.children previous stored key child)
    · exact generated
  · apply List.pairwise_append.mpr
    refine ⟨invariant.keyDistinct, fresh_distinct known found, ?_⟩
    intro old present current recent same
    subst current
    exact disjoint old present recent

/-- Empty fresh targets close the full accumulated table, including the final batch. -/
theorem finish (states : List State) (rows : Automaton State Symbol)
    (known found : List (List State)) (choices : List (Choice State Symbol))
    (invariant : Invariant states rows known found choices) (empty : fresh known found = []) :
    Closed states rows (known ++ fresh known found) choices := by
  have pendingKnown : ∀ key ∈ found, key ∈ known := by
    intro key member
    by_cases old : key ∈ known
    · exact old
    · have recent := (mem_fresh known found key).mpr ⟨member, old⟩
      rw [empty] at recent
      cases recent
  simpa only [empty, List.append_nil] using
    close states rows known found choices invariant pendingKnown

/-- Every successful concrete discovery evaluation derives its final closed table. -/
theorem evaluation_closed (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known found : List (List State)) (choices : List (Choice State Symbol))
    (calls : Nat) (result : Outcome (List State) (List (Choice State Symbol)))
    (execution : Evaluation limit (step states rows) known found choices calls result)
    (finalKnown : List (List State)) (finalChoices : List (Choice State Symbol))
    (returned : result = .ready finalKnown finalChoices)
    (invariant : Invariant states rows known found choices) :
    Closed states rows finalKnown finalChoices := by
  revert invariant
  induction execution with
  | limit_exceeded => cases returned
  | done within empty =>
      intro invariant
      cases returned
      exact finish states rows _ _ _ invariant empty
  | next within nonempty following ih =>
      intro invariant
      exact ih returned (advance states rows _ _ _ invariant nonempty)

/-- Concrete discovery always has a finite evaluation within the original limit plus one. -/
theorem compile_complete (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    ∃ calls, calls ≤ limit + 1 ∧
      Evaluation limit (step states rows) [] (targets states rows (initial states rows))
        (initial states rows) calls (compile limit states rows) ∧
      compile limit states rows ≠ .exhausted :=
  SourceSizedDeterminizationDiscovery.complete limit (step states rows)
    (targets states rows (initial states rows)) (initial states rows)

/-- Successful bounded discovery supplies closure without a caller-supplied invariant. -/
theorem compile_closed (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) : Closed states rows known choices := by
  obtain ⟨calls, _, execution, _⟩ := compile_complete limit states rows
  exact evaluation_closed limit states rows [] _ _ calls _ execution known choices returned
    (initial_invariant states rows)

/-- Successful discovery preserves the original language at every original root state. -/
theorem compile_language (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) (state : State) (term : Term Symbol) :
    Accepts rows state term ↔
      ∃ key ∈ known, state ∈ key ∧ Accepts (emittedRows states rows choices) key term :=
  accepted_iff states rows plain supported known choices
    (compile_closed limit states rows known choices returned) state term

/-- Successful discovery also derives every subset count class's uniqueness. -/
theorem compile_unique (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) :
    SizedRank.Unambiguous (emittedRows states rows choices) :=
  SourceSizedDeterminizationClosure.classes_unique states rows plain supported known choices
    (compile_closed limit states rows known choices returned)

end MicroCFTA.SourceSizedDeterminizationRun
