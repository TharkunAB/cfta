import MicroCFTA.RecursiveUnambiguous

/-!
# Language and uniqueness of emitted deterministic rows

The source is `Gen.Internal.Table.deterministicRows`. A transition records its
symbol and tuple of child subsets. Its target is the set of original owners
whose transition matches that tuple. The finite original key list supplies a
canonical list view of each set. The source map and set iteration supply the
order of emitted transitions; this module does not identify it with the
original reference order.

These laws apply to the emitted rows. The bounded discovery loop must still
derive their completeness and the absence of repeated transition tuples.
-/
namespace MicroCFTA.SourceSizedDeterminizationKernel
open Language

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

/-- Check every child position, including the common arity from the source token. -/
def childrenMatch : List State → List (List State) → Bool
  | [], [] => true
  | state :: states, key :: keys => decide (state ∈ key) && childrenMatch states keys
  | _, _ => false

/-- Matching means that each original child belongs to its corresponding subset. -/
theorem childrenMatch_iff (states : List State) (keys : List (List State)) :
    childrenMatch states keys = true ↔ All₂ (fun state key => state ∈ key) states keys := by
  induction states generalizing keys with
  | nil =>
      cases keys with
      | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
      | cons key keys => constructor <;> intro h <;> cases h
  | cons state states ih =>
      cases keys with
      | nil => constructor <;> intro h <;> cases h
      | cons key keys =>
          constructor
          · intro passed
            simp only [childrenMatch, Bool.and_eq_true, decide_eq_true_eq] at passed
            exact .cons passed.1 ((ih keys).mp passed.2)
          · intro related
            cases related with
            | cons member rest => simp [childrenMatch, member, (ih keys).mpr rest]

/-- Compute the target subset from all original owners of the matching token. -/
def target (states : List State) (rows : Automaton State Symbol)
    (symbol : Symbol) (keys : List (List State)) : List State :=
  states.filter fun state => (rows state).any fun edge =>
    decide (edge.label = symbol) && childrenMatch edge.children keys

/-- The target retains exactly the matching original transition owners. -/
theorem mem_target (states : List State) (rows : Automaton State Symbol)
    (symbol : Symbol) (keys : List (List State)) (state : State) :
    state ∈ target states rows symbol keys ↔ state ∈ states ∧
      ∃ edge ∈ rows state, edge.label = symbol ∧
        All₂ (fun child key => child ∈ key) edge.children keys := by
  simp only [target, List.mem_filter, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, childrenMatch_iff]

omit [DecidableEq State] [DecidableEq Symbol] in
private theorem child_runs (rows : Automaton State Symbol)
    (keys : List (List State)) (terms : List (Term Symbol))
    (exact : All₂ (fun key term => ∀ state, state ∈ key ↔ Accepts rows state term) keys terms)
    (states : List State) :
    All₂ (fun state key => state ∈ key) states keys ↔ All₂ (Accepts rows) states terms := by
  induction exact generalizing states with
  | nil =>
      cases states with
      | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
      | cons state states => constructor <;> intro h <;> cases h
  | @cons key term keys terms head tail ih =>
      cases states with
      | nil => constructor <;> intro h <;> cases h
      | cons state states =>
          constructor
          · intro related
            cases related with
            | cons member rest => exact .cons ((head state).mp member) ((ih states).mp rest)
          · intro related
            cases related with
            | cons accepted rest => exact .cons ((head state).mpr accepted) ((ih states).mpr rest)

/-- Exact child subsets make the target exactly the original node's accepting states. -/
theorem target_exact (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (symbol : Symbol) (keys : List (List State)) (terms : List (Term Symbol))
    (exact : All₂ (fun key term => ∀ state, state ∈ key ↔ Accepts rows state term) keys terms)
    (state : State) :
    state ∈ target states rows symbol keys ↔ Accepts rows state (.node symbol terms) := by
  rw [mem_target, accepts_node_iff]
  constructor
  · rintro ⟨_, edge, member, label, children⟩
    exact ⟨edge, member, label, (child_runs rows keys terms exact edge.children).mp children,
      plain state edge member _⟩
  · rintro ⟨edge, member, label, children, _⟩
    exact ⟨supported state edge member, edge, member, label,
      (child_runs rows keys terms exact edge.children).mpr children⟩

/-- The canonical list of original states that accept a term is a proof specification. -/
noncomputable def acceptingKey (states : List State) (rows : Automaton State Symbol)
    (term : Term Symbol) : List State := by
  classical
  exact states.filter fun state => decide (Accepts rows state term)

omit [DecidableEq State] [DecidableEq Symbol] in
/-- A complete owner list loses no original accepting state. -/
theorem mem_acceptingKey (states : List State) (rows : Automaton State Symbol)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (term : Term Symbol) (state : State) :
    state ∈ acceptingKey states rows term ↔ Accepts rows state term := by
  classical
  simp only [acceptingKey, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro accepted
    refine ⟨?_, accepted⟩
    cases accepted with
    | node edge terms member _ _ => exact supported state edge member

/-- The operational target calculation gives the canonical semantic subset. -/
theorem target_key (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (symbol : Symbol) (keys : List (List State)) (terms : List (Term Symbol))
    (exact : All₂ (fun key term => ∀ state, state ∈ key ↔ Accepts rows state term) keys terms) :
    target states rows symbol keys = acceptingKey states rows (.node symbol terms) := by
  classical
  unfold target acceptingKey
  apply List.filter_congr
  intro state inside
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro found
    exact decide_eq_true ((target_exact states rows plain supported symbol keys terms exact state).mp
      (List.mem_filter.mpr ⟨inside, found⟩))
  · intro accepted
    exact (List.mem_filter.mp
      ((target_exact states rows plain supported symbol keys terms exact state).mpr
        (of_decide_eq_true accepted))).2

/-- A source emission retains the symbol and all ordered child subsets. -/
abbrev Choice (State Symbol : Type) := Symbol × List (List State)

/-- Read the emitted transitions of one deterministic subset. -/
def emittedRows (states : List State) (rows : Automaton State Symbol)
    (choices : List (Choice State Symbol)) : Automaton (List State) Symbol :=
  fun key => (choices.filter fun entry => decide (target states rows entry.1 entry.2 = key)).map
    fun entry => ⟨entry.1, entry.2, fun _ => true⟩

/-- Every finite run in emitted rows has exactly its original accepting-state subset. -/
theorem accepted_key (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (choices : List (Choice State Symbol)) (term : Term Symbol) (key : List State)
    (accepted : Accepts (emittedRows states rows choices) key term) :
    key = acceptingKey states rows term := by
  have result := Term.rec
    (motive_1 := fun term => ∀ key, Accepts (emittedRows states rows choices) key term →
      key = acceptingKey states rows term)
    (motive_2 := fun terms => ∀ keys, All₂ (Accepts (emittedRows states rows choices)) keys terms →
      All₂ (fun key term => ∀ state, state ∈ key ↔ Accepts rows state term) keys terms) ?_ ?_ ?_ term
  · exact result key accepted
  · intro symbol terms ih key accepted
    obtain ⟨edge, member, label, children, _⟩ :=
      (accepts_node_iff (emittedRows states rows choices) key symbol terms).mp accepted
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    change entry.1 = symbol at label
    have same := of_decide_eq_true (List.mem_filter.mp present).2
    calc
      key = target states rows entry.1 entry.2 := same.symm
      _ = acceptingKey states rows (.node entry.1 terms) :=
        target_key states rows plain supported _ _ _ (ih _ children)
      _ = acceptingKey states rows (.node symbol terms) := by rw [label]
  · intro keys related
    cases related
    exact .nil
  · intro term terms head tail keys related
    cases related with
    | cons accepted rest =>
      exact .cons (fun state => by
        rw [head _ accepted]
        exact mem_acceptingKey states rows supported term state) (tail _ rest)

/-- Emitted subset acceptance gives both directions of membership in the original language. -/
theorem accepted_exact (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (choices : List (Choice State Symbol)) (term : Term Symbol) (key : List State)
    (accepted : Accepts (emittedRows states rows choices) key term) (state : State) :
    state ∈ key ↔ Accepts rows state term := by
  rw [accepted_key states rows plain supported choices term key accepted]
  exact mem_acceptingKey states rows supported term state

/-- Two subset runs of the same term have the same canonical key. -/
theorem accepted_unique (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (choices : List (Choice State Symbol)) (term : Term Symbol) (first second : List State)
    (left : Accepts (emittedRows states rows choices) first term)
    (right : Accepts (emittedRows states rows choices) second term) : first = second :=
  (accepted_key states rows plain supported choices term first left).trans
    (accepted_key states rows plain supported choices term second right).symm

private theorem child_keys_unique (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (choices : List (Choice State Symbol)) (terms : List (Term Symbol))
    (first second : List (List State))
    (left : All₂ (Accepts (emittedRows states rows choices)) first terms)
    (right : All₂ (Accepts (emittedRows states rows choices)) second terms) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons accepted rest ih =>
      cases right with
      | cons other others =>
        rw [accepted_unique states rows plain supported choices _ _ _ accepted other, ih _ others]

/-- Distinct emitted token/tuple pairs give disjoint alternatives at every subset. -/
theorem rows_disjoint (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (choices : List (Choice State Symbol)) (distinct : choices.Nodup) (key : List State) :
    RecursiveUnambiguous.DisjointRows (emittedRows states rows choices) key := by
  unfold RecursiveUnambiguous.DisjointRows emittedRows
  apply List.pairwise_map.mpr
  apply (distinct.filter _).imp
  intro first second different term left right
  obtain ⟨leftTerms, leftEq, leftRuns, _⟩ := left
  obtain ⟨rightTerms, rightEq, rightRuns, _⟩ := right
  obtain ⟨sameLabel, sameTerms⟩ := Term.node.inj (leftEq.symm.trans rightEq)
  rw [← sameTerms] at rightRuns
  exact different (Prod.ext sameLabel
    (child_keys_unique states rows plain supported choices _ _ _ leftRuns rightRuns))

/-- The source count recurrence is unambiguous on distinct emitted deterministic tuples. -/
theorem classes_unique (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (choices : List (Choice State Symbol)) (distinct : choices.Nodup) :
    SizedRank.Unambiguous (emittedRows states rows choices) := by
  have plainOutput : Decoder.Plain (emittedRows states rows choices) := by
    intro key edge member term
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    rfl
  intro key size
  exact RecursiveUnambiguous.enumerate_nodup _ plainOutput (fun _ => True) (by simp)
    (fun key _ => rows_disjoint states rows plain supported choices distinct key) size key trivial

end MicroCFTA.SourceSizedDeterminizationKernel
