import MicroCFTA.SourceSizedDeterminizationKernel

/-!
# Completeness of closed deterministic discovery

The discovery loop must cover every original transition over known child
keys. Once every pending target is known, its emitted rows preserve the
original language. These are internal discovery invariants.
-/
namespace MicroCFTA.SourceSizedDeterminizationClosure
open Language SourceSizedDeterminizationKernel

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

/-- Discovery retains complete choices, known children, and scheduled targets. -/
structure Invariant (states : List State) (rows : Automaton State Symbol)
    (known pending : List (List State)) (choices : List (Choice State Symbol)) : Prop where
  covered : ∀ state ∈ states, ∀ edge ∈ rows state, ∀ keys,
    All₂ (fun child key => key ∈ known ∧ child ∈ key) edge.children keys →
      (edge.label, keys) ∈ choices
  children : ∀ choice ∈ choices, ∀ key ∈ choice.2, key ∈ known
  targets : ∀ choice ∈ choices,
    target states rows choice.1 choice.2 ∈ known ∨
      target states rows choice.1 choice.2 ∈ pending
  distinct : choices.Nodup
  keyDistinct : known.Nodup

/-- Closed discovery has no outstanding target keys. -/
def Closed (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol)) : Prop :=
  Invariant states rows known [] choices

/-- Pending entries already known can be removed without losing coverage. -/
theorem close (states : List State) (rows : Automaton State Symbol)
    (known pending : List (List State)) (choices : List (Choice State Symbol))
    (invariant : Invariant states rows known pending choices)
    (completed : ∀ key ∈ pending, key ∈ known) : Closed states rows known choices := by
  refine ⟨invariant.covered, invariant.children, ?_, invariant.distinct, invariant.keyDistinct⟩
  intro choice member
  exact Or.inl ((invariant.targets choice member).elim id (completed _))

/-- Each original accepting run has an emitted run at a known deterministic key. -/
theorem accepted_complete (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states rows known choices) (term : Term Symbol) (state : State)
    (accepted : Accepts rows state term) :
    ∃ key ∈ known, state ∈ key ∧ Accepts (emittedRows states rows choices) key term := by
  have result := Term.rec
    (motive_1 := fun term => ∀ state, Accepts rows state term →
      ∃ key ∈ known, state ∈ key ∧ Accepts (emittedRows states rows choices) key term)
    (motive_2 := fun terms => ∀ children, All₂ (Accepts rows) children terms →
      ∃ keys, All₂ (fun child key => key ∈ known ∧ child ∈ key) children keys ∧
        All₂ (Accepts (emittedRows states rows choices)) keys terms) ?_ ?_ ?_ term
  · exact result state accepted
  · intro symbol terms ih state accepted
    obtain ⟨edge, member, label, children, _⟩ :=
      (accepts_node_iff rows state symbol terms).mp accepted
    obtain ⟨keys, related, runs⟩ := ih edge.children children
    have chosen : (symbol, keys) ∈ choices := by
      simpa only [label] using closed.covered state (supported state edge member) edge member keys related
    have finalKnown : target states rows symbol keys ∈ known := by
      rcases closed.targets (symbol, keys) chosen with present | impossible
      · exact present
      · cases impossible
    have exactChildren : All₂ (fun key term => ∀ state,
        state ∈ key ↔ Accepts rows state term) keys terms :=
      All₂.imp (fun key term run =>
        SourceSizedDeterminizationKernel.accepted_exact states rows plain supported choices term key run) runs
    have inside : state ∈ target states rows symbol keys :=
      (target_exact states rows plain supported symbol keys terms exactChildren state).mpr accepted
    have emitted : (⟨symbol, keys, fun _ => true⟩ : Edge (List State) Symbol) ∈
        emittedRows states rows choices (target states rows symbol keys) := by
      apply List.mem_map.mpr
      exact ⟨(symbol, keys), List.mem_filter.mpr ⟨chosen, by simp⟩, rfl⟩
    exact ⟨_, finalKnown, inside, .node _ terms emitted runs rfl⟩
  · intro children related
    cases related
    exact ⟨[], .nil, .nil⟩
  · intro term terms head tail children related
    cases related with
    | cons accepted rest =>
        obtain ⟨key, present, inside, run⟩ := head _ accepted
        obtain ⟨keys, related, runs⟩ := tail _ rest
        exact ⟨key :: keys, .cons ⟨present, inside⟩ related, .cons run runs⟩

/-- Closed emitted rows retain exactly the original accepted terms at their member states. -/
theorem accepted_iff (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states rows known choices) (state : State) (term : Term Symbol) :
    Accepts rows state term ↔
      ∃ key ∈ known, state ∈ key ∧ Accepts (emittedRows states rows choices) key term := by
  constructor
  · exact accepted_complete states rows plain supported known choices closed term state
  · rintro ⟨key, _, member, accepted⟩
    exact (SourceSizedDeterminizationKernel.accepted_exact
      states rows plain supported choices term key accepted state).mp member

/-- Closed discovery supplies the distinct choices needed by the kernel count law. -/
theorem classes_unique (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (closed : Closed states rows known choices) :
    SizedRank.Unambiguous (emittedRows states rows choices) :=
  SourceSizedDeterminizationKernel.classes_unique states rows plain supported choices closed.distinct

end MicroCFTA.SourceSizedDeterminizationClosure
