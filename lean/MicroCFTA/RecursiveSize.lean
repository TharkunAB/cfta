import MicroCFTA.Decoder
import MicroCFTA.Sparse

/-!
# Exact node-count classes of recursive plain automata

Each transition contributes one node. Children are added in order by a
convolution of the built built with the next child. This is the arithmetic
and order used by `Gen.Internal.Table.stateTable`.

The reference recurrence is total: every child of a size `n + 1` term uses a
size at most `n`. States can form arbitrary cycles. The proofs concern this
finite recurrence, not the productivity of Haskell's shared lazy size lists.
-/

namespace MicroCFTA.RecursiveSize

open Language

/-- Count all nodes of a finite tree. -/
def nodeSize {Symbol : Type} : Term Symbol → Nat
  | .node _ children => children.foldr (fun child size => nodeSize child + size) 0 + 1

/-- Count all nodes in an ordered child forest. -/
def forestSize {Symbol : Type} (children : List (Term Symbol)) : Nat :=
  children.foldr (fun child size => nodeSize child + size) 0

/-- Every tree consumes at least its root node. -/
theorem nodeSize_pos {Symbol : Type} (term : Term Symbol) : 0 < nodeSize term := by
  cases term
  simp [nodeSize]

/-- Concatenating child forests adds their node counts. -/
theorem forestSize_append {Symbol : Type} (left right : List (Term Symbol)) :
    forestSize (left ++ right) = forestSize left + forestSize right := by
  induction left with
  | nil => simp [forestSize]
  | cons term rest ih =>
      change nodeSize term + forestSize (rest ++ right) =
        (nodeSize term + forestSize rest) + forestSize right
      rw [ih, Nat.add_assoc]

/-- One more child adds exactly its node count. -/
theorem forestSize_snoc {Symbol : Type} (children : List (Term Symbol)) (child : Term Symbol) :
    forestSize (children ++ [child]) = forestSize children + nodeSize child := by
  rw [forestSize_append]
  simp [forestSize]

/-- Prove a list property by appending one element at a time. -/
theorem snoc_induction {α : Type} {P : List α → Prop} (empty : P [])
    (step : ∀ built item, P built → P (built ++ [item])) (items : List α) : P items := by
  have reversed : ∀ xs : List α, P xs.reverse := by
    intro xs
    induction xs with
    | nil => exact empty
    | cons item rest ih => simpa using step rest.reverse item ih
  simpa using reversed items.reverse

/-- A relation on an appended state exposes its last related child. -/
theorem all₂_snoc_iff {State Symbol : Type} (R : State → Term Symbol → Prop)
    (states : List State) (state : State) (terms : List (Term Symbol)) :
    All₂ R (states ++ [state]) terms ↔
      ∃ built child, terms = built ++ [child] ∧ All₂ R states built ∧ R state child := by
  induction states generalizing terms with
  | nil =>
      constructor
      · intro related
        cases related with
        | cons child tail =>
            cases tail
            exact ⟨[], _, rfl, .nil, child⟩
      · rintro ⟨built, child, rfl, related, accepted⟩
        cases related
        exact .cons accepted .nil
  | cons first rest ih =>
      constructor
      · intro related
        cases related with
        | cons accepted remaining =>
            obtain ⟨built, child, rfl, related, last⟩ := (ih _).mp remaining
            exact ⟨_ :: built, child, rfl, .cons accepted related, last⟩
      · rintro ⟨built, child, rfl, related, accepted⟩
        cases related with
        | cons firstAccepted tail =>
            exact .cons firstAccepted ((ih _).mpr ⟨_, child, rfl, tail, accepted⟩)

/-- Add a child by ascending built size, then built-major Cartesian order. -/
def extendForests {Symbol : Type} (prefixes : Nat → List (List (Term Symbol)))
    (children : Nat → List (Term Symbol)) (size : Nat) : List (List (Term Symbol)) :=
  (List.range (size + 1)).flatMap fun prefixSize =>
    (prefixes prefixSize).flatMap fun built =>
      (children (size - prefixSize)).map fun child => built ++ [child]

/-- The empty child list has one forest of size zero and none at other sizes. -/
def emptyForests {Symbol : Type} (size : Nat) : List (List (Term Symbol)) :=
  if size = 0 then [[]] else []

/-- Build exact-size child forests by the same left-to-right built products as Table. -/
def forests {State Symbol : Type} (children : Nat → State → List (Term Symbol))
    (states : List State) : Nat → List (List (Term Symbol)) :=
  states.foldl (fun prefixes state => extendForests prefixes (fun size => children size state))
    emptyForests

/-- Appending a state performs one built-product step. -/
theorem forests_snoc {State Symbol : Type} (children : Nat → State → List (Term Symbol))
    (states : List State) (state : State) :
    forests children (states ++ [state]) =
      extendForests (forests children states) (fun size => children size state) := by
  simp [forests, List.foldl_append]

/-- Prefix convolution implements exact forest acceptance and node-count addition. -/
theorem mem_extendForests_iff {State Symbol : Type}
    (R : State → Term Symbol → Prop) (states : List State) (state : State)
    (prefixes : Nat → List (List (Term Symbol))) (children : Nat → List (Term Symbol))
    (bound : Nat)
    (prefixExact : ∀ size, size ≤ bound → ∀ terms,
      terms ∈ prefixes size ↔ All₂ R states terms ∧ forestSize terms = size)
    (childExact : ∀ size, size ≤ bound → ∀ term,
      term ∈ children size ↔ R state term ∧ nodeSize term = size)
    (size : Nat) (within : size ≤ bound) (terms : List (Term Symbol)) :
    terms ∈ extendForests prefixes children size ↔
      All₂ R (states ++ [state]) terms ∧ forestSize terms = size := by
  constructor
  · intro member
    obtain ⟨prefixSize, prefixBound, built, prefixMember, child, childMember, same⟩ :=
      (by simpa [extendForests, List.mem_flatMap, List.mem_map] using member :
        ∃ prefixSize, prefixSize < size + 1 ∧ ∃ built, built ∈ prefixes prefixSize ∧
          ∃ child, child ∈ children (size - prefixSize) ∧ built ++ [child] = terms)
    have hp := (prefixExact prefixSize (by omega) built).mp prefixMember
    have hc := (childExact (size - prefixSize) (by omega) child).mp childMember
    subst terms
    refine ⟨(all₂_snoc_iff R states state _).mpr ⟨built, child, rfl, hp.1, hc.1⟩, ?_⟩
    rw [forestSize_snoc, hp.2, hc.2]
    omega
  · rintro ⟨related, exactSize⟩
    obtain ⟨built, child, rfl, acceptedPrefix, acceptedChild⟩ :=
      (all₂_snoc_iff R states state terms).mp related
    rw [forestSize_snoc] at exactSize
    have prefixBound : forestSize built ≤ size := by omega
    have childSize : nodeSize child = size - forestSize built := by omega
    apply List.mem_flatMap.mpr
    refine ⟨forestSize built, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨built, (prefixExact _ (by omega) _).mpr ⟨acceptedPrefix, rfl⟩, ?_⟩
    exact List.mem_map.mpr ⟨child,
      (childExact _ (by omega) _).mpr ⟨acceptedChild, childSize⟩, rfl⟩

/-- Child-built enumeration is exact whenever all required child classes are exact. -/
theorem mem_forests_iff {State Symbol : Type}
    (R : State → Term Symbol → Prop) (children : Nat → State → List (Term Symbol))
    (bound : Nat)
    (childExact : ∀ size, size ≤ bound → ∀ state term,
      term ∈ children size state ↔ R state term ∧ nodeSize term = size)
    (states : List State) (size : Nat) (within : size ≤ bound) (terms : List (Term Symbol)) :
    terms ∈ forests children states size ↔ All₂ R states terms ∧ forestSize terms = size := by
  induction states using snoc_induction generalizing size terms with
  | empty =>
      constructor
      · intro member
        simp only [forests, List.foldl_nil, emptyForests] at member
        split at member
        next zero =>
          have same : terms = [] := by simpa using member
          subst terms
          exact ⟨.nil, by simp [forestSize, zero]⟩
        next => simp at member
      · rintro ⟨related, exactSize⟩
        cases related
        simpa [forests, emptyForests, forestSize] using exactSize.symm
  | step states state ih =>
      rw [forests_snoc]
      exact mem_extendForests_iff R states state (forests children states)
        (fun size => children size state) bound
        (fun size within terms => ih size within terms)
        (fun size within term => childExact size within state term) size within terms

/-- Enumerate accepting runs with exactly the requested number of tree nodes.
Only smaller child sizes are read, so recursive state graphs do not affect termination. -/
def enumerate {State Symbol : Type} (A : Automaton State Symbol)
    (size : Nat) (state : State) : List (Term Symbol) :=
  match size with
  | 0 => []
  | budget + 1 => (A state).flatMap fun edge =>
      (forests (fun childSize childState =>
        if _smaller : childSize ≤ budget then enumerate A childSize childState else [])
        edge.children budget).map (Term.node edge.label)
termination_by size

/-- Exact node-count enumeration has no terms at size zero. -/
theorem enumerate_zero {State Symbol : Type} (A : Automaton State Symbol) (state : State) :
    enumerate A 0 state = [] := by rw [enumerate]

/-- Exact node-count enumeration is sound and complete for plain cyclic graphs. -/
theorem mem_enumerate_iff {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (size : Nat) (state : State) (term : Term Symbol) :
    term ∈ enumerate A size state ↔ Accepts A state term ∧ nodeSize term = size := by
  induction size using Nat.strongRecOn generalizing state term with
  | ind size ih =>
      cases size with
      | zero =>
          constructor
          · simp [enumerate_zero]
          · rintro ⟨_, exactSize⟩
            have positive := nodeSize_pos term
            omega
      | succ budget =>
          let children := fun childSize childState =>
            if _smaller : childSize ≤ budget then enumerate A childSize childState else []
          have childExact : ∀ childSize, childSize ≤ budget → ∀ childState child,
              child ∈ children childSize childState ↔
                Accepts A childState child ∧ nodeSize child = childSize := by
            intro childSize smaller childState child
            simp only [children, dite_eq_left smaller]
            exact ih childSize (by omega) childState child
          constructor
          · intro member
            rw [enumerate] at member
            obtain ⟨edge, edgeMember, terms, forestMember, same⟩ :=
              (by simpa [children, List.mem_flatMap, List.mem_map] using member :
                ∃ edge, edge ∈ A state ∧ ∃ terms,
                  terms ∈ forests children edge.children budget ∧ .node edge.label terms = term)
            have exactForest := (mem_forests_iff (Accepts A) children budget childExact
              edge.children budget (Nat.le_refl _) terms).mp forestMember
            subst term
            refine ⟨.node edge terms edgeMember exactForest.1 (plain state edge edgeMember _), ?_⟩
            simp only [nodeSize]
            change forestSize terms + 1 = budget + 1
            rw [exactForest.2]
          · rintro ⟨accepted, exactSize⟩
            cases accepted with
            | node edge terms edgeMember acceptedChildren guard =>
                have forestExact : forestSize terms = budget := by
                  simpa [nodeSize, forestSize] using exactSize
                rw [enumerate]
                apply List.mem_flatMap.mpr
                refine ⟨edge, edgeMember, List.mem_map.mpr ⟨terms, ?_, rfl⟩⟩
                exact (mem_forests_iff (Accepts A) children budget childExact
                  edge.children budget (Nat.le_refl _) terms).mpr ⟨acceptedChildren, forestExact⟩

/-- Sum one constant contribution for every list member. -/
theorem sum_constant (items : List α) (value : Nat) :
    (items.map fun _ => value).sum = items.length * value := by
  induction items with
  | nil => simp
  | cons item rest ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- Add a child count by finite convolution over all built-prefix sizes. -/
def extendCounts (prefixes children : Nat → Nat) (size : Nat) : Nat :=
  ((List.range (size + 1)).map fun builtSize =>
    prefixes builtSize * children (size - builtSize)).sum

/-- The empty forest has one replay position at size zero. -/
def emptyCount (size : Nat) : Nat := if size = 0 then 1 else 0

/-- Count a sequence of children by repeated built-prefix convolution. -/
def forestCounts {State : Type} (children : Nat → State → Nat)
    (states : List State) : Nat → Nat :=
  states.foldl (fun prefixes state => extendCounts prefixes (fun size => children size state))
    emptyCount

/-- An appended child causes one additional counting convolution. -/
theorem forestCounts_snoc {State : Type} (children : Nat → State → Nat)
    (states : List State) (state : State) :
    forestCounts children (states ++ [state]) =
      extendCounts (forestCounts children states) (fun size => children size state) := by
  simp [forestCounts, List.foldl_append]

/-- The counting convolution counts all Cartesian child extensions. -/
theorem length_extendForests {Symbol : Type}
    (prefixes : Nat → List (List (Term Symbol))) (children : Nat → List (Term Symbol))
    (size : Nat) :
    (extendForests prefixes children size).length =
      extendCounts (fun size => (prefixes size).length) (fun size => (children size).length) size := by
  simp only [extendForests, List.length_flatMap, List.length_map, extendCounts]
  apply congrArg List.sum
  apply List.map_congr_left
  intro builtSize _
  exact sum_constant (prefixes builtSize) (children (size - builtSize)).length

/-- Child-forest counts agree with their independent list enumeration. -/
theorem length_forests {State Symbol : Type}
    (children : Nat → State → List (Term Symbol)) (states : List State) (size : Nat) :
    (forests children states size).length =
      forestCounts (fun size state => (children size state).length) states size := by
  induction states using snoc_induction generalizing size with
  | empty =>
      by_cases zero : size = 0 <;> simp [forests, forestCounts, emptyForests, emptyCount, zero]
  | step states state ih =>
      simp only [forests_snoc, forestCounts_snoc, length_extendForests, ih]

/-- Count exact node-size runs without constructing any Cartesian term lists. -/
def countAt {State Symbol : Type} (A : Automaton State Symbol)
    (size : Nat) (state : State) : Nat :=
  match size with
  | 0 => 0
  | budget + 1 => ((A state).map fun edge =>
      forestCounts (fun childSize childState =>
        if _smaller : childSize ≤ budget then countAt A childSize childState else 0)
        edge.children budget).sum
termination_by size

/-- The exact node-size counter equals the number of enumerated accepting runs. -/
theorem countAt_correct {State Symbol : Type} (A : Automaton State Symbol)
    (size : Nat) (state : State) : countAt A size state = (enumerate A size state).length := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [countAt, enumerate]; rfl
      | succ budget =>
          rw [countAt, enumerate]
          simp only [List.length_flatMap, List.length_map, length_forests]
          apply congrArg List.sum
          apply List.map_congr_left
          intro edge _
          have countsEqual :
              (fun childSize childState =>
                if _smaller : childSize ≤ budget then countAt A childSize childState else 0) =
              (fun childSize childState =>
                (if _smaller : childSize ≤ budget then enumerate A childSize childState else []).length) := by
            funext childSize childState
            by_cases smaller : childSize ≤ budget
            · simp only [dite_eq_left smaller]
              exact ih childSize (by omega) childState
            · simp [smaller]
          rw [countsEqual]

/-- The plan for an empty forest at one exact size. -/
def emptyForestPlan {Symbol : Type} (size : Nat) : Decoder.Plan (List (Term Symbol)) :=
  if size = 0 then .source [[]] else .source []

/-- Compile one prefix convolution into choices and mixed-radix applications. -/
def extendForestPlans {Symbol : Type}
    (prefixes : Nat → Decoder.Plan (List (Term Symbol)))
    (children : Nat → Decoder.Plan (Term Symbol)) (size : Nat) : Decoder.Plan (List (Term Symbol)) :=
  Decoder.choices ((List.range (size + 1)).map fun builtSize =>
    .ap (.map (fun built child => built ++ [child]) (prefixes builtSize))
      (children (size - builtSize)))

/-- Compile all child-prefix products without enumerating their terms. -/
def forestPlans {State Symbol : Type} (children : Nat → State → Decoder.Plan (Term Symbol))
    (states : List State) : Nat → Decoder.Plan (List (Term Symbol)) :=
  states.foldl (fun prefixes state => extendForestPlans prefixes (fun size => children size state))
    emptyForestPlan

/-- Appending a child adds one plan convolution. -/
theorem forestPlans_snoc {State Symbol : Type}
    (children : Nat → State → Decoder.Plan (Term Symbol)) (states : List State) (state : State) :
    forestPlans children (states ++ [state]) =
      extendForestPlans (forestPlans children states) (fun size => children size state) := by
  simp [forestPlans, List.foldl_append]

/-- Prefix plans preserve the precise split and Cartesian order of enumeration. -/
theorem values_extendForestPlans {Symbol : Type}
    (prefixes : Nat → Decoder.Plan (List (Term Symbol)))
    (children : Nat → Decoder.Plan (Term Symbol)) (size : Nat) :
    Decoder.values (extendForestPlans prefixes children size) =
      extendForests (fun size => Decoder.values (prefixes size))
        (fun size => Decoder.values (children size)) size := by
  simp [extendForestPlans, Decoder.values_choices, List.flatMap_map,
    Decoder.values, Decoder.applyValues, extendForests]

/-- Child plans preserve every replay position of the exact forest enumeration. -/
theorem values_forestPlans {State Symbol : Type}
    (children : Nat → State → Decoder.Plan (Term Symbol)) (states : List State) (size : Nat) :
    Decoder.values (forestPlans children states size) =
      forests (fun size state => Decoder.values (children size state)) states size := by
  induction states using snoc_induction generalizing size with
  | empty =>
      by_cases zero : size = 0 <;>
        simp [forestPlans, forests, emptyForestPlan, emptyForests, Decoder.values, zero]
  | step states state ih =>
      simp only [forestPlans_snoc, forests_snoc, values_extendForestPlans, ih]

/-- Compile one exact node-size class of an arbitrary cyclic plain graph. -/
def compileAt {State Symbol : Type} (A : Automaton State Symbol)
    (size : Nat) (state : State) : Decoder.Plan (Term Symbol) :=
  match size with
  | 0 => .source []
  | budget + 1 => Decoder.choices ((A state).map fun edge =>
      .map (Term.node edge.label)
        (forestPlans (fun childSize childState =>
          if _smaller : childSize ≤ budget then compileAt A childSize childState else .source [])
          edge.children budget))
termination_by size

/-- Exact-size compilation preserves branch order and accepting-run multiplicity. -/
theorem values_compileAt {State Symbol : Type} (A : Automaton State Symbol)
    (size : Nat) (state : State) : Decoder.values (compileAt A size state) = enumerate A size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [compileAt, enumerate]; rfl
      | succ budget =>
          rw [compileAt, enumerate]
          simp only [Decoder.values_choices, List.flatMap_map, Decoder.values, values_forestPlans]
          have childrenEqual :
              (fun childSize childState => Decoder.values
                (if _smaller : childSize ≤ budget then compileAt A childSize childState else .source [])) =
              (fun childSize childState =>
                if _smaller : childSize ≤ budget then enumerate A childSize childState else []) := by
            funext childSize childState
            by_cases smaller : childSize ≤ budget
            · simp only [dite_eq_left smaller]
              exact ih childSize (by omega) childState
            · simp [smaller, Decoder.values]
          rw [childrenEqual]

/-- Compiled plan cardinality equals the independently computed size recurrence. -/
theorem count_compileAt {State Symbol : Type} (A : Automaton State Symbol)
    (size : Nat) (state : State) : Decoder.count (compileAt A size state) = countAt A size state := by
  rw [Decoder.count_correct, values_compileAt, countAt_correct]

/-- The normalized mixed-radix decoder returns the same exact-size replay list entry. -/
theorem decode_compileAt {State Symbol : Type} (A : Automaton State Symbol)
    (size : Nat) (state : State) (rank : Nat) :
    Decoder.decode (Decoder.normalize (compileAt A size state)) rank = (enumerate A size state)[rank]? := by
  rw [Decoder.decode_normalize, Decoder.decode_correct, values_compileAt]

/-- Every accepted term has a rank exactly in its node-size class, and every rank is sound. -/
theorem compiled_coverage {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (size : Nat) (state : State) (term : Term Symbol) :
    (∃ rank, rank < countAt A size state ∧
      Decoder.decode (Decoder.normalize (compileAt A size state)) rank = some term) ↔
      Accepts A state term ∧ nodeSize term = size := by
  rw [← mem_enumerate_iff A plain]
  constructor
  · rintro ⟨rank, _, decoded⟩
    rw [decode_compileAt] at decoded
    exact List.mem_of_getElem? decoded
  · intro member
    obtain ⟨rank, bound, decoded⟩ := List.mem_iff_getElem.mp member
    exact ⟨rank, by simpa [countAt_correct] using bound,
      by rw [decode_compileAt, List.getElem?_eq_getElem bound, decoded]⟩

/-- One counting convolution reads only input sizes up to its output size. -/
theorem extendCounts_congr (left right left' right' : Nat → Nat) (bound : Nat)
    (sameLeft : ∀ size, size ≤ bound → left size = left' size)
    (sameRight : ∀ size, size ≤ bound → right size = right' size)
    (size : Nat) (within : size ≤ bound) :
    extendCounts left right size = extendCounts left' right' size := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro builtSize member
  have fits := List.mem_range.mp member
  rw [sameLeft builtSize (by omega), sameRight (size - builtSize) (by omega)]

/-- All child-prefix convolutions read only child sizes up to the forest size. -/
theorem forestCounts_congr {State : Type} (left right : Nat → State → Nat)
    (bound : Nat) (same : ∀ size, size ≤ bound → ∀ state, left size state = right size state)
    (states : List State) (size : Nat) (within : size ≤ bound) :
    forestCounts left states size = forestCounts right states size := by
  induction states using snoc_induction generalizing size with
  | empty => rfl
  | step states state ih =>
      rw [forestCounts_snoc, forestCounts_snoc]
      exact extendCounts_congr _ _ _ _ bound ih (fun size h => same size h state) size within

/-- The checked decreasing definition satisfies the ordinary uncapped size recurrence. -/
theorem countAt_succ {State Symbol : Type} (A : Automaton State Symbol)
    (budget : Nat) (state : State) :
    countAt A (budget + 1) state =
      ((A state).map fun edge => forestCounts (countAt A) edge.children budget).sum := by
  rw [countAt]
  apply congrArg List.sum
  apply List.map_congr_left
  intro edge _
  exact forestCounts_congr _ _ budget
    (fun size smaller state => by simp [smaller]) edge.children budget (Nat.le_refl _)

/-- Equations for exact node-size counts: zero at size zero and one root node per edge. -/
def CountRecurrence {State Symbol : Type} (A : Automaton State Symbol)
    (counts : Nat → State → Nat) : Prop :=
  (∀ state, counts 0 state = 0) ∧
    ∀ budget state, counts (budget + 1) state =
      ((A state).map fun edge => forestCounts counts edge.children budget).sum

/-- The constructed counter is a solution of the node-size recurrence. -/
theorem countAt_solves {State Symbol : Type} (A : Automaton State Symbol) :
    CountRecurrence A (countAt A) :=
  ⟨fun state => by rw [countAt], countAt_succ A⟩

/-- Decreasing child sizes make the node-count recurrence have a unique solution. -/
theorem countRecurrence_unique {State Symbol : Type} (A : Automaton State Symbol)
    (counts : Nat → State → Nat) (solves : CountRecurrence A counts)
    (size : Nat) (state : State) : counts size state = countAt A size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [solves.1 state, countAt]
      | succ budget =>
          rw [solves.2 budget state, countAt_succ]
          apply congrArg List.sum
          apply List.map_congr_left
          intro edge _
          exact forestCounts_congr _ _ budget
            (fun childSize smaller childState => ih childSize (by omega) childState)
            edge.children budget (Nat.le_refl _)

/-- An exact-size count is positive exactly when that class has an accepted term. -/
theorem countAt_positive_iff {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (size : Nat) (state : State) :
    0 < countAt A size state ↔ ∃ term, Accepts A state term ∧ nodeSize term = size := by
  rw [countAt_correct, List.length_pos_iff_exists_mem]
  constructor
  · rintro ⟨term, member⟩
    exact ⟨term, (mem_enumerate_iff A plain size state term).mp member⟩
  · rintro ⟨term, accepted⟩
    exact ⟨term, (mem_enumerate_iff A plain size state term).mpr accepted⟩

/-- A finite prefix of a coefficient function, including zero coefficients. -/
def tabulate (counts : Nat → Nat) (length : Nat) : Sparse.Series Nat :=
  (List.range length).map fun size => (size, counts size)

/-- Natural ranges have strictly increasing entries. -/
theorem range_ordered (length : Nat) : (List.range length).Pairwise (· < ·) := by
  induction length with
  | zero => simp
  | succ length ih =>
      rw [List.range_succ]
      apply List.pairwise_append.mpr
      refine ⟨ih, by simp, ?_⟩
      intro left member right last
      have same : right = length := by simpa using last
      subst right
      exact List.mem_range.mp member

/-- Tabulated size prefixes satisfy sparse lookup's strict-order requirement. -/
theorem tabulate_ordered (counts : Nat → Nat) (length : Nat) :
    Sparse.Ordered (tabulate counts length) :=
  List.pairwise_map.mpr (range_ordered length)

/-- A tabulated split sum is its direct finite sum over size indexes. -/
theorem splitSum_tabulated (sizes : List Nat) (counts : Nat → Nat)
    (right : Sparse.Series Nat) (wanted : Nat) :
    Sparse.splitSum (sizes.map fun size => (size, counts size)) right wanted =
      (sizes.map fun size => if size ≤ wanted then
        counts size * Sparse.coefficient right (wanted - size) else 0).sum := by
  induction sizes with
  | nil => rfl
  | cons size rest ih => simp [Sparse.splitSum, ih]

/-- The Haskell-shaped sparse convolution computes one exact child-prefix recurrence.
The right finite series can omit zero classes, provided its coefficients are the child counts. -/
theorem sparse_prefix_convolution (prefixes : Nat → Nat) (children : Sparse.Series Nat)
    (ordered : Sparse.Ordered children) (size : Nat) :
    Sparse.valueAtSize (Sparse.mulSparse (tabulate prefixes (size + 1)) children) size =
      extendCounts prefixes (Sparse.coefficient children) size := by
  rw [Sparse.sparse_split_correct _ _ (tabulate_ordered _ _) ordered]
  rw [tabulate, splitSum_tabulated]
  apply congrArg List.sum
  apply List.map_congr_left
  intro builtSize member
  have smaller : builtSize ≤ size := by have := List.mem_range.mp member; omega
  simp only [smaller, ↓reduceIte]

/-- Enumerate all node-size classes up to a bound in ascending size order. -/
def enumerateAtMost {State Symbol : Type} (A : Automaton State Symbol)
    (bound : Nat) (state : State) : List (Term Symbol) :=
  (List.range (bound + 1)).flatMap fun size => enumerate A size state

/-- Node-size bounded enumeration contains exactly the bounded accepted terms. -/
theorem mem_enumerateAtMost_iff {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (bound : Nat) (state : State) (term : Term Symbol) :
    term ∈ enumerateAtMost A bound state ↔ Accepts A state term ∧ nodeSize term ≤ bound := by
  constructor
  · intro member
    obtain ⟨size, range, inside⟩ := List.mem_flatMap.mp member
    have accepted := (mem_enumerate_iff A plain size state term).mp inside
    have fits := List.mem_range.mp range
    exact ⟨accepted.1, by omega⟩
  · rintro ⟨accepted, fits⟩
    exact List.mem_flatMap.mpr ⟨nodeSize term, List.mem_range.mpr (by omega),
      (mem_enumerate_iff A plain _ state term).mpr ⟨accepted, rfl⟩⟩

/-- Every accepted finite term occurs at its own node-count class. -/
theorem accepted_at_own_size {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (state : State) (term : Term Symbol) (accepted : Accepts A state term) :
    term ∈ enumerate A (nodeSize term) state :=
  (mem_enumerate_iff A plain _ state term).mpr ⟨accepted, rfl⟩

/-- Exact-size decoding eventually reaches every accepted finite term of a cyclic graph. -/
theorem accepted_iff_has_rank {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (state : State) (term : Term Symbol) :
    Accepts A state term ↔ ∃ size rank, rank < countAt A size state ∧
      Decoder.decode (Decoder.normalize (compileAt A size state)) rank = some term := by
  constructor
  · intro accepted
    obtain ⟨rank, bounded, decoded⟩ :=
      (compiled_coverage A plain (nodeSize term) state term).mpr ⟨accepted, rfl⟩
    exact ⟨nodeSize term, rank, bounded, decoded⟩
  · rintro ⟨size, rank, bounded, decoded⟩
    exact ((compiled_coverage A plain size state term).mp ⟨rank, bounded, decoded⟩).1

/-- The height of a finite term never exceeds its node count. -/
theorem height_le_nodeSize {Symbol : Type} (term : Term Symbol) : term.height ≤ nodeSize term := by
  induction term using Term.rec
    (motive_2 := fun (terms : List (Term Symbol)) => forestHeight terms ≤ forestSize terms) with
  | node symbol terms ih =>
      simp only [Term.height, nodeSize]
      exact Nat.succ_le_succ ih
  | nil => exact Nat.le_refl _
  | cons term terms first rest =>
      change max term.height (forestHeight terms) ≤ nodeSize term + forestSize terms
      apply Nat.max_le.mpr
      constructor <;> omega

/-- Exact node-size enumeration refines the existing height-bounded reference semantics. -/
theorem exact_size_in_height_bound {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (size : Nat) (state : State) (term : Term Symbol)
    (member : term ∈ enumerate A size state) : term ∈ Language.enumerate A size state := by
  have accepted := (mem_enumerate_iff A plain size state term).mp member
  apply (Language.mem_enumerate_iff A size state term).mpr
  exact ⟨accepted.1, by have := height_le_nodeSize term; omega⟩

/-- Compile all classes up to a bound in ascending node-count order. -/
def compileAtMost {State Symbol : Type} (A : Automaton State Symbol)
    (bound : Nat) (state : State) : Decoder.Plan (Term Symbol) :=
  Decoder.choices ((List.range (bound + 1)).map fun size => compileAt A size state)

/-- Count all classes up to a bound without constructing the terms. -/
def countAtMost {State Symbol : Type} (A : Automaton State Symbol)
    (bound : Nat) (state : State) : Nat :=
  ((List.range (bound + 1)).map fun size => countAt A size state).sum

/-- The global finite plan has exactly the size-major list semantics. -/
theorem values_compileAtMost {State Symbol : Type} (A : Automaton State Symbol)
    (bound : Nat) (state : State) :
    Decoder.values (compileAtMost A bound state) = enumerateAtMost A bound state := by
  simp [compileAtMost, Decoder.values_choices, List.flatMap_map, values_compileAt, enumerateAtMost]

/-- Global plan cardinality is the sum of the exact class counts. -/
theorem count_compileAtMost {State Symbol : Type} (A : Automaton State Symbol)
    (bound : Nat) (state : State) :
    Decoder.count (compileAtMost A bound state) = countAtMost A bound state := by
  simp [compileAtMost, Decoder.count_choices, List.map_map, Function.comp_def,
    count_compileAt, countAtMost]

/-- The sum of class counts is the number of bounded accepting runs. -/
theorem countAtMost_correct {State Symbol : Type} (A : Automaton State Symbol)
    (bound : Nat) (state : State) :
    countAtMost A bound state = (enumerateAtMost A bound state).length := by
  rw [← count_compileAtMost, Decoder.count_correct, values_compileAtMost]

/-- Every global decoder result agrees with the ordered bounded enumeration. -/
theorem decode_compileAtMost {State Symbol : Type} (A : Automaton State Symbol)
    (bound : Nat) (state : State) (rank : Nat) :
    Decoder.decode (Decoder.normalize (compileAtMost A bound state)) rank =
      (enumerateAtMost A bound state)[rank]? := by
  rw [Decoder.decode_normalize, Decoder.decode_correct, values_compileAtMost]

/-- Bounded size-major replay has exactly the accepted support within the node-count bound. -/
theorem bounded_compiled_coverage {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (bound : Nat) (state : State) (term : Term Symbol) :
    (∃ rank, rank < countAtMost A bound state ∧
      Decoder.decode (Decoder.normalize (compileAtMost A bound state)) rank = some term) ↔
      Accepts A state term ∧ nodeSize term ≤ bound := by
  rw [← mem_enumerateAtMost_iff A plain]
  constructor
  · rintro ⟨rank, _, decoded⟩
    rw [decode_compileAtMost] at decoded
    exact List.mem_of_getElem? decoded
  · intro member
    obtain ⟨rank, bounded, decoded⟩ := List.mem_iff_getElem.mp member
    exact ⟨rank, by simpa [countAtMost_correct] using bounded,
      by rw [decode_compileAtMost, List.getElem?_eq_getElem bounded, decoded]⟩

/-- The global offset of a size class is the sum of all smaller class counts. -/
def classOffset {State Symbol : Type} (A : Automaton State Symbol)
    (size : Nat) (state : State) : Nat :=
  ((List.range size).map fun smaller => countAt A smaller state).sum

/-- List concatenation uses the sum of preceding class lengths as its rank offset. -/
theorem get_class_offset (classes : Nat → List α) (bound size rank : Nat)
    (within : size ≤ bound) (valid : rank < (classes size).length) :
    ((List.range (bound + 1)).flatMap classes)[((List.range size).map fun n => (classes n).length).sum + rank]? = (classes size)[rank]? := by
  induction bound generalizing size with
  | zero =>
      have : size = 0 := by omega
      subst size
      simp
  | succ bound ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      by_cases earlier : size ≤ bound
      · have previous := ih size earlier valid
        have found :
            ((List.range (bound + 1)).flatMap classes)[((List.range size).map fun n => (classes n).length).sum + rank]? =
              some (classes size)[rank] := by
          rw [previous, List.getElem?_eq_getElem valid]
        have fits := (List.getElem?_eq_some_iff.mp found).1
        rw [List.getElem?_append_left fits]
        exact previous
      · have same : size = bound + 1 := by omega
        subst size
        have length : ((List.range (bound + 1)).flatMap classes).length =
            ((List.range (bound + 1)).map fun n => (classes n).length).sum :=
          List.length_flatMap
        rw [List.getElem?_append_right (by rw [length]; omega), length]
        simp

/-- A valid class rank replays at its canonical size-major offset under any larger bound. -/
theorem sizeMajor_rank_replay {State Symbol : Type} (A : Automaton State Symbol)
    (bound size : Nat) (state : State) (rank : Nat)
    (within : size ≤ bound) (valid : rank < countAt A size state) :
    Decoder.decode (Decoder.normalize (compileAtMost A bound state))
      (classOffset A size state + rank) =
      Decoder.decode (Decoder.normalize (compileAt A size state)) rank := by
  rw [decode_compileAtMost, decode_compileAt, classOffset]
  simp only [countAt_correct]
  exact get_class_offset (fun size => enumerate A size state) bound size rank within
    (by simpa [countAt_correct] using valid)

/-- Exact-size classes contain only terms of their own node count. -/
theorem filter_class_size {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (actual wanted : Nat) (state : State) :
    (enumerate A actual state).filter (fun term => decide (nodeSize term = wanted)) =
      if actual = wanted then enumerate A actual state else [] := by
  by_cases same : actual = wanted
  · rw [ite_eq_left same]
    apply List.filter_eq_self.mpr
    intro term member
    have exactSize := ((mem_enumerate_iff A plain actual state term).mp member).2
    simp [exactSize, same]
  · rw [ite_eq_right same]
    apply List.filter_eq_nil_iff.mpr
    intro term member accepted
    have exactSize := ((mem_enumerate_iff A plain actual state term).mp member).2
    exact same (exactSize.symm.trans (of_decide_eq_true accepted))

/-- Filtering the bounded list by node size recovers exactly that class, with multiplicity. -/
theorem filter_bounded_size {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (bound size : Nat) (state : State) (within : size ≤ bound) :
    (enumerateAtMost A bound state).filter (fun term => decide (nodeSize term = size)) =
      enumerate A size state := by
  induction bound generalizing size with
  | zero =>
      have : size = 0 := by omega
      subst size
      simp [enumerateAtMost, enumerate_zero]
  | succ bound ih =>
      have expanded : enumerateAtMost A (bound + 1) state =
          enumerateAtMost A bound state ++ enumerate A (bound + 1) state := by
        simp only [enumerateAtMost, List.range_succ, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [expanded, List.filter_append, filter_class_size A plain]
      by_cases earlier : size ≤ bound
      · have different : bound + 1 ≠ size := by omega
        rw [ite_eq_right different, ih size earlier, List.append_nil]
      · have same : size = bound + 1 := by omega
        subst size
        rw [ite_eq_left rfl]
        have empty : (enumerateAtMost A bound state).filter
            (fun term => decide (nodeSize term = bound + 1)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro term member matched
          have small := ((mem_enumerateAtMost_iff A plain bound state term).mp member).2
          have large := of_decide_eq_true matched
          omega
        rw [empty, List.nil_append]

/-- Uniform size-major run sampling has exact event count divided by the total run count. -/
theorem bounded_event_probability {State Symbol : Type} (A : Automaton State Symbol)
    (bound : Nat) (state : State) (event : Term Symbol → Bool) :
    Probability.eventMass event
      (Probability.normalize (Probability.counting
        (Decoder.values (Decoder.normalize (compileAtMost A bound state))))) =
      ((enumerateAtMost A bound state).countP event : Rat) / countAtMost A bound state := by
  rw [Decoder.values_normalize, values_compileAtMost,
    Probability.uniform_event_probability, countAtMost_correct]

/-- A size class receives its run count divided by the count of all bounded classes. -/
theorem size_class_probability {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (bound size : Nat) (state : State) (within : size ≤ bound) :
    Probability.eventMass (fun term => decide (nodeSize term = size))
      (Probability.normalize (Probability.counting
        (Decoder.values (Decoder.normalize (compileAtMost A bound state))))) =
      (countAt A size state : Rat) / countAtMost A bound state := by
  rw [bounded_event_probability, List.countP_eq_length_filter,
    filter_bounded_size A plain bound size state within, countAt_correct]

/-- A nonempty bounded language gives a normalized finite probability distribution. -/
theorem bounded_probability_normalized {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (bound : Nat) (state : State) (term : Term Symbol)
    (accepted : Accepts A state term) (within : nodeSize term ≤ bound) :
    Probability.IsProbability
      (Probability.normalize (Probability.counting
        (Decoder.values (Decoder.normalize (compileAtMost A bound state))))) := by
  rw [Decoder.values_normalize, values_compileAtMost]
  apply Probability.uniform_probability
  exact List.length_pos_iff_exists_mem.mpr
    ⟨term, (mem_enumerateAtMost_iff A plain bound state term).mpr ⟨accepted, within⟩⟩

/-- Structural productivity of a plain state is equivalent to a nonempty exact size class. -/
theorem productive_iff_positive_class {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (state : State) :
    (∃ term, Accepts A state term) ↔ ∃ size, 0 < countAt A size state := by
  constructor
  · rintro ⟨term, accepted⟩
    exact ⟨nodeSize term,
      (countAt_positive_iff A plain (nodeSize term) state).mpr ⟨term, accepted, rfl⟩⟩
  · rintro ⟨size, positive⟩
    obtain ⟨term, accepted, _⟩ := (countAt_positive_iff A plain size state).mp positive
    exact ⟨term, accepted⟩

/-- Removing a state with no accepted finite tree removes only zero count classes. -/
theorem empty_iff_zero_classes {State Symbol : Type} (A : Automaton State Symbol)
    (plain : Decoder.Plain A) (state : State) :
    (¬∃ term, Accepts A state term) ↔ ∀ size, countAt A size state = 0 := by
  rw [productive_iff_positive_class A plain state]
  constructor
  · intro empty size
    have notPositive : ¬0 < countAt A size state := fun positive => empty ⟨size, positive⟩
    omega
  · intro zero ⟨size, positive⟩
    rw [zero size] at positive
    omega

end MicroCFTA.RecursiveSize
