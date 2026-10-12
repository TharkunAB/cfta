import MicroCFTA.Language
import MicroCFTA.DistinctRank
import MicroCFTA.MinimumSize

/-!
# Source overlap checks before compact automaton indexing

The source compares each edge with every later edge. Equal root labels and
arities can overlap only when every pair of corresponding child languages
overlaps. Constraints can remove terms but cannot invalidate this implication.
-/
namespace MicroCFTA.AutomatonAmbiguity
open Language

/-- One edge's language with its actual complete-term guard retained. -/
def EdgeLanguage (domain : State → Term Symbol → Prop) (edge : Edge State Symbol)
    (term : Term Symbol) : Prop :=
  ∃ children, term = .node edge.label children ∧ All₂ domain edge.children children ∧ edge.guard term = true

/-- Source zipWith followed by and. Arity is checked separately. -/
def childOverlap (test : State → State → Bool) (left right : List State) : Bool :=
  ((left.zip right).map (fun pair => test pair.1 pair.2)).all id

/-- Exact source Boolean overlap test, including its arity guard. -/
def overlapping [DecidableEq Symbol] (test : State → State → Bool)
    (left right : Edge State Symbol) : Bool :=
  decide (left.label = right.label) && decide (left.children.length = right.children.length) &&
    childOverlap test left.children right.children

/-- Execute the source tails scan in its original pair order. -/
def ambiguous [DecidableEq Symbol] (test : State → State → Bool) : List (Edge State Symbol) → Bool
  | [] => false
  | first :: rest => rest.any (overlapping test first) || ambiguous test rest

/-- Shared children force every tested position to report possible overlap. -/
theorem children_overlap (domain : State → Term Symbol → Prop) (test : State → State → Bool)
    (covers : ∀ left right term, domain left term → domain right term → test left right = true)
    (left right : List State) (terms : List (Term Symbol))
    (first : All₂ domain left terms) (second : All₂ domain right terms) :
    childOverlap test left right = true := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons state term states terms accepted rest ih =>
      cases second with
      | cons other later =>
          change (test state _ && childOverlap test states _) = true
          simp [covers _ _ _ accepted other, ih _ later]

/-- A common accepted term is never missed by a sound child overlap test. -/
theorem common_detected [DecidableEq Symbol] (domain : State → Term Symbol → Prop)
    (test : State → State → Bool)
    (covers : ∀ left right term, domain left term → domain right term → test left right = true)
    (left right : Edge State Symbol) (term : Term Symbol)
    (first : EdgeLanguage domain left term) (second : EdgeLanguage domain right term) :
    overlapping test left right = true := by
  obtain ⟨leftTerms, leftShape, leftRuns, _⟩ := first
  obtain ⟨rightTerms, rightShape, rightRuns, _⟩ := second
  have shapes := Term.node.inj (leftShape.symm.trans rightShape)
  rcases shapes with ⟨symbols, terms⟩
  subst rightTerms
  have lengths := leftRuns.length_eq.trans rightRuns.length_eq.symm
  simp [overlapping, symbols, lengths, children_overlap domain test covers _ _ _ leftRuns rightRuns]

/-- A false source test proves disjoint edge languages, even with constraints. -/
theorem overlap_false_disjoint [DecidableEq Symbol] (domain : State → Term Symbol → Prop)
    (test : State → State → Bool)
    (covers : ∀ left right term, domain left term → domain right term → test left right = true)
    (left right : Edge State Symbol) (separate : overlapping test left right = false) :
    ∀ term, EdgeLanguage domain left term → ¬ EdgeLanguage domain right term := by
  intro term first second
  have detected := common_detected domain test covers left right term first second
  simp [separate] at detected

/-- The source pair scan succeeds exactly when every ordered edge pair is separate. -/
theorem ambiguous_false [DecidableEq Symbol] (test : State → State → Bool)
    (edges : List (Edge State Symbol)) :
    ambiguous test edges = false ↔
      edges.Pairwise (fun left right => overlapping test left right = false) := by
  induction edges with
  | nil => simp [ambiguous]
  | cons first rest ih => simp [ambiguous, ih, List.pairwise_cons, List.any_eq_false]

/-- Passing the compact-plan gate gives pairwise disjoint accepted alternatives. -/
theorem compact_disjoint [DecidableEq Symbol] (domain : State → Term Symbol → Prop)
    (test : State → State → Bool)
    (covers : ∀ left right term, domain left term → domain right term → test left right = true)
    (edges : List (Edge State Symbol)) (accepted : ambiguous test edges = false) :
    edges.Pairwise (fun left right => ∀ term, EdgeLanguage domain left term → ¬ EdgeLanguage domain right term) := by
  exact ((ambiguous_false test edges).mp accepted).imp
    (fun separate => overlap_false_disjoint domain test covers _ _ separate)

/-- Successful pairwise intersection tests construct a complete common child tuple. -/
theorem children_witness (domain : State → Term Symbol → Prop) (test : State → State → Bool)
    (witness : ∀ left right, test left right = true → ∃ term, domain left term ∧ domain right term)
    (left right : List State) (lengths : left.length = right.length)
    (found : childOverlap test left right = true) :
    ∃ terms, All₂ domain left terms ∧ All₂ domain right terms := by
  induction left generalizing right with
  | nil =>
      have empty : right = [] := List.length_eq_zero_iff.mp lengths.symm
      subst right
      exact ⟨[], .nil, .nil⟩
  | cons first rest ih =>
      cases right with
      | nil => simp at lengths
      | cons other later =>
          have heads : test first other = true ∧ childOverlap test rest later = true := by
            simpa [childOverlap] using found
          obtain ⟨term, leftRun, rightRun⟩ := witness first other heads.1
          obtain ⟨terms, leftRuns, rightRuns⟩ := ih later (by simpa using lengths) heads.2
          exact ⟨term :: terms, .cons leftRun leftRuns, .cons rightRun rightRuns⟩

/-- Without edge constraints the overlap test is exact, not only conservative. -/
theorem plain_overlap_exact [DecidableEq Symbol] (domain : State → Term Symbol → Prop)
    (test : State → State → Bool)
    (covers : ∀ left right term, domain left term → domain right term → test left right = true)
    (witness : ∀ left right, test left right = true → ∃ term, domain left term ∧ domain right term)
    (left right : Edge State Symbol) (plainLeft : ∀ term, left.guard term = true)
    (plainRight : ∀ term, right.guard term = true) :
    overlapping test left right = true ↔ ∃ term, EdgeLanguage domain left term ∧ EdgeLanguage domain right term := by
  constructor
  · intro found
    have facts : (left.label = right.label ∧ left.children.length = right.children.length) ∧
        childOverlap test left.children right.children = true := by simpa [overlapping] using found
    obtain ⟨terms, first, second⟩ := children_witness domain test witness _ _ facts.1.2 facts.2
    exact ⟨.node left.label terms, ⟨terms, rfl, first, plainLeft _⟩,
      ⟨terms, by rw [facts.1.1], second, plainRight _⟩⟩
  · rintro ⟨term, first, second⟩
    exact common_detected domain test covers left right term first second

/-- Intersection correctness supplies the needed negative-soundness interface. -/
theorem intersect_test_covers (domain : State → Term Symbol → Prop)
    (intersect : State → State → State) (productive : State → Bool)
    (exact : ∀ left right term, domain (intersect left right) term ↔ domain left term ∧ domain right term)
    (retains : ∀ state term, domain state term → productive state = true) :
    ∀ left right term, domain left term → domain right term → productive (intersect left right) = true := by
  intro left right term first second
  exact retains _ _ ((exact left right term).mpr ⟨first, second⟩)

/-- Source productiveRows checks for a row, then for a computed minimum-size entry. -/
def productiveRows [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) (state : State) : Bool :=
  if (automaton state).isEmpty then false
  else (MinimumSize.minimumSizes automaton states complete state).isSome

/-- The actual minimum-size test never rejects an accepted finite term. -/
theorem productiveRows_covers [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) (state : State) (term : Term Symbol)
    (accepted : Accepts automaton state term) : productiveRows automaton states complete state = true := by
  obtain ⟨size, found, _⟩ := MinimumSize.minimumSizes_complete automaton states complete accepted
  have row : (automaton state).isEmpty = false := by
    cases accepted with
    | node edge terms member runs guard =>
        cases entries : automaton state with
        | nil => simp [entries] at member
        | cons first rest => rfl
  simp [productiveRows, row, found]

/-- Successful minimum-size lookup supplies an accepted witness for plain graphs. -/
theorem productiveRows_witness [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states)
    (state : State) (found : productiveRows automaton states complete state = true) :
    ∃ term, Accepts automaton state term := by
  unfold productiveRows at found
  split at found
  · contradiction
  · cases minimum : MinimumSize.minimumSizes automaton states complete state with
    | none => simp [minimum] at found
    | some size =>
        obtain ⟨term, accepted, _⟩ := MinimumSize.minimumSizes_sound automaton plain states complete state size minimum
        exact ⟨term, accepted⟩

/-- The explicit synchronous intersection of plain graphs has no residual guard. -/
theorem intersect_plain [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) : Decoder.Plain (Language.intersect automaton automaton) := by
  intro pair edge member term
  obtain ⟨left, leftMember, right, rightMember, _, _, shape⟩ :=
    (mem_intersect_iff automaton automaton pair.1 pair.2 edge).mp member
  subst edge
  simp [plain _ left leftMember term, plain _ right rightMember term]

/-- The source minimum-size check on intersections discharges the overlap premise. -/
theorem table_test_covers [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (states : List (State × State))
    (complete : ∀ state, state ∈ states) (left right : State) (term : Term Symbol)
    (first : Accepts automaton left term) (second : Accepts automaton right term) :
    productiveRows (Language.intersect automaton automaton) states complete (left, right) = true :=
  productiveRows_covers _ states complete _ term (intersect_complete automaton automaton first right second)

/-- For plain cyclic graphs, successful overlap checks produce an actual common term. -/
theorem table_test_witness [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (states : List (State × State)) (complete : ∀ state, state ∈ states)
    (left right : State)
    (found : productiveRows (Language.intersect automaton automaton) states complete (left, right) = true) :
    ∃ term, Accepts automaton left term ∧ Accepts automaton right term := by
  obtain ⟨term, accepted⟩ := productiveRows_witness _ (intersect_plain automaton plain) states complete _ found
  exact ⟨term, (accepts_intersect_iff automaton automaton left right term).mp accepted⟩

/-- A passing row gate has disjoint languages from computed intersection minima. -/
theorem table_gate_disjoint [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (states : List (State × State))
    (complete : ∀ state, state ∈ states) (edges : List (Edge State Symbol))
    (accepted : ambiguous (fun left right =>
      productiveRows (Language.intersect automaton automaton) states complete (left, right)) edges = false) :
    edges.Pairwise (fun left right => ∀ term,
      EdgeLanguage (Accepts automaton) left term → ¬EdgeLanguage (Accepts automaton) right term) :=
  compact_disjoint (Accepts automaton) _ (table_test_covers automaton states complete) edges accepted

/-- The compact alternative concatenation has no repeated terms. -/
theorem compact_nodup [DecidableEq Symbol] (domain : State → Term Symbol → Prop)
    (test : State → State → Bool)
    (covers : ∀ left right term, domain left term → domain right term → test left right = true)
    (edges : List (Edge State Symbol)) (accepted : ambiguous test edges = false)
    (outputs : Edge State Symbol → List (Term Symbol))
    (sound : ∀ edge ∈ edges, ∀ term ∈ outputs edge, EdgeLanguage domain edge term)
    (unique : ∀ edge ∈ edges, (outputs edge).Nodup) :
    (edges.flatMap outputs).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨unique, ?_⟩
  apply (compact_disjoint domain test covers edges accepted).imp_of_mem
  intro left right leftMember rightMember separate first firstMember second secondMember same
  subst second
  exact separate first (sound left leftMember first firstMember) (sound right rightMember first secondMember)

/-- Complete edge callbacks compose into the compact node's exact distinct index. -/
def compactIndex [DecidableEq Symbol] (domain : State → Term Symbol → Prop)
    (test : State → State → Bool)
    (covers : ∀ left right term, domain left term → domain right term → test left right = true)
    (edges : List (Edge State Symbol)) (accepted : ambiguous test edges = false)
    (outputs : Edge State Symbol → List (Term Symbol))
    (exact : ∀ edge ∈ edges, ∀ term, term ∈ outputs edge ↔ EdgeLanguage domain edge term)
    (unique : ∀ edge ∈ edges, (outputs edge).Nodup) :
    DistinctRank.Index (fun term => ∃ edge ∈ edges, EdgeLanguage domain edge term) where
  members := edges.flatMap outputs
  nodup := compact_nodup domain test covers edges accepted outputs
    (fun edge member term found => (exact edge member term).mp found) unique
  exact term := by
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨edge, member, found⟩
      exact ⟨edge, member, (exact edge member term).mp found⟩
    · rintro ⟨edge, member, found⟩
      exact ⟨edge, member, (exact edge member term).mpr found⟩

/-- Compact counting adds local distinct counts after the source overlap gate. -/
theorem compact_count [DecidableEq Symbol] (domain : State → Term Symbol → Prop)
    (test : State → State → Bool)
    (covers : ∀ left right term, domain left term → domain right term → test left right = true)
    (edges : List (Edge State Symbol)) (accepted : ambiguous test edges = false)
    (outputs : Edge State Symbol → List (Term Symbol))
    (exact : ∀ edge ∈ edges, ∀ term, term ∈ outputs edge ↔ EdgeLanguage domain edge term)
    (unique : ∀ edge ∈ edges, (outputs edge).Nodup) :
    (compactIndex domain test covers edges accepted outputs exact unique).count =
      (edges.map (fun edge => (outputs edge).length)).sum := by
  simp [DistinctRank.Index.count, compactIndex, List.length_flatMap]

end MicroCFTA.AutomatonAmbiguity
