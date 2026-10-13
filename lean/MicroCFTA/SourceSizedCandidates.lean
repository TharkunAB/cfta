import MicroCFTA.RecursiveSize

/-!
# The exact ordered candidate worker in `Data.CFTA.Sized`

The worker visits reversed children. It splits the available node count in
ascending left-size order. It visits each left forest before the terms of
the current child. Reversing the result restores the source child order.
-/

namespace MicroCFTA.SourceSizedCandidates

open Language RecursiveSize

/-- Build reversed argument lists in the order of the source `go` worker. -/
def go {State Symbol : Type} (classAt : State → Nat → List (Term Symbol)) :
    List State → Nat → List (List (Term Symbol))
  | [], remaining => if remaining = 0 then [[]] else []
  | current :: before, remaining =>
      (List.range (remaining + 1)).flatMap fun left =>
        (go classAt before left).flatMap fun arguments =>
          (classAt current (remaining - left)).map fun term => term :: arguments

/-- Build terms of one positive node count. Zero cannot contain a tree. -/
def candidates {State Symbol : Type} (classAt : State → Nat → List (Term Symbol))
    (label : Symbol) (children : List State) : Nat → List (Term Symbol)
  | 0 => []
  | remaining + 1 =>
      (go classAt children.reverse remaining).map fun arguments => .node label arguments.reverse

/-- Reversed traversal is the same ordered nested product as the count table. -/
theorem go_reverse_eq_forests {State Symbol : Type}
    (classAt : State → Nat → List (Term Symbol)) (states : List State) (remaining : Nat) :
    (go classAt states remaining).map List.reverse =
      forests (fun size state => classAt state size) states.reverse remaining := by
  induction states generalizing remaining with
  | nil => simp [go, forests, emptyForests]; split <;> rfl
  | cons current before ih =>
      simp only [go, List.map_flatMap, List.map_map, Function.comp_def,
        List.reverse_cons, forests_snoc, extendForests]
      apply congrArg (List.flatMap · (List.range (remaining + 1)))
      funext left
      rw [← ih]
      simp only [List.flatMap_map]

/-- Candidate order agrees with the forward count-table forest recurrence. -/
theorem candidates_succ {State Symbol : Type}
    (classAt : State → Nat → List (Term Symbol)) (label : Symbol)
    (children : List State) (remaining : Nat) :
    candidates classAt label children (remaining + 1) =
      (forests (fun size state => classAt state size) children remaining).map (.node label) := by
  rw [← List.reverse_reverse children]
  rw [← go_reverse_eq_forests]
  simp only [candidates, List.map_map, Function.comp_def, List.reverse_reverse]

/-- All child queries are strictly smaller than the requested parent size. -/
theorem child_size_lt {remaining left : Nat} (member : left ∈ List.range (remaining + 1)) :
    left < remaining + 1 ∧ remaining - left < remaining + 1 := by
  have := List.mem_range.mp member
  omega

/-- Exact child classes make the candidate list exact before its guard. -/
theorem mem_candidates_succ_iff {State Symbol : Type}
    (R : State → Term Symbol → Prop) (classAt : State → Nat → List (Term Symbol))
    (bound : Nat)
    (childExact : ∀ size, size ≤ bound → ∀ state term,
      term ∈ classAt state size ↔ R state term ∧ nodeSize term = size)
    (label : Symbol) (children : List State) (remaining : Nat) (within : remaining ≤ bound)
    (term : Term Symbol) :
    term ∈ candidates classAt label children (remaining + 1) ↔
      ∃ arguments, term = .node label arguments ∧ All₂ R children arguments ∧
        nodeSize term = remaining + 1 := by
  rw [candidates_succ]
  constructor
  · intro member
    obtain ⟨arguments, forestMember, same⟩ := List.mem_map.mp member
    subst term
    have exactForest := (mem_forests_iff R (fun size state => classAt state size)
      bound childExact children remaining within arguments).mp forestMember
    exact ⟨arguments, rfl, exactForest.1, by
      simp only [nodeSize]
      change forestSize arguments + 1 = remaining + 1
      rw [exactForest.2]⟩
  · rintro ⟨arguments, rfl, related, size⟩
    apply List.mem_map.mpr
    refine ⟨arguments, ?_, rfl⟩
    apply (mem_forests_iff R (fun size state => classAt state size)
      bound childExact children remaining within arguments).mpr
    exact ⟨related, by simpa [nodeSize, forestSize] using size⟩

/-- The worker reads child classes only up to its remaining node count. -/
theorem go_congr {State Symbol : Type}
    (first second : State → Nat → List (Term Symbol)) (states : List State)
    (remaining : Nat)
    (agree : ∀ state size, size ≤ remaining → first state size = second state size) :
    go first states remaining = go second states remaining := by
  induction states generalizing remaining with
  | nil => rfl
  | cons current before ih =>
      simp only [go]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro left member
      have bound : left ≤ remaining := by have := List.mem_range.mp member; omega
      rw [ih left (fun state size within => agree state size (Nat.le_trans within bound))]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro arguments _
      rw [agree current (remaining - left) (Nat.sub_le _ _)]

/-- A candidate query reads only classes strictly below the parent size. -/
theorem candidates_congr {State Symbol : Type}
    (first second : State → Nat → List (Term Symbol)) (label : Symbol)
    (children : List State) (size : Nat)
    (agree : ∀ state childSize, childSize < size → first state childSize = second state childSize) :
    candidates first label children size = candidates second label children size := by
  cases size with
  | zero => rfl
  | succ remaining =>
      simp only [candidates]
      rw [go_congr first second children.reverse remaining
        (fun state size within => agree state size (by omega))]

/-- The argument worker reads only states in its child list. -/
theorem go_congr_children {State Symbol : Type}
    (first second : State → Nat → List (Term Symbol)) (states : List State)
    (remaining : Nat)
    (agree : ∀ state ∈ states, ∀ size, size ≤ remaining → first state size = second state size) :
    go first states remaining = go second states remaining := by
  induction states generalizing remaining with
  | nil => rfl
  | cons current before ih =>
      simp only [go]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro left member
      have bound : left ≤ remaining := by have := List.mem_range.mp member; omega
      rw [ih left (fun state present size within =>
        agree state (List.mem_cons_of_mem _ present) size (Nat.le_trans within bound))]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro arguments _
      rw [agree current (by simp) (remaining - left) (Nat.sub_le _ _)]

/-- Candidate agreement needs only its actual children at smaller sizes. -/
theorem candidates_congr_children {State Symbol : Type}
    (first second : State → Nat → List (Term Symbol)) (label : Symbol)
    (children : List State) (size : Nat)
    (agree : ∀ state ∈ children, ∀ childSize, childSize < size →
      first state childSize = second state childSize) :
    candidates first label children size = candidates second label children size := by
  cases size with
  | zero => rfl
  | succ remaining =>
      simp only [candidates]
      rw [go_congr_children first second children.reverse remaining]
      intro state member childSize within
      exact agree state (List.mem_reverse.mp member) childSize (by omega)

/-- One empty child state makes every argument combination empty. -/
theorem go_nil_of_child {State Symbol : Type}
    (classAt : State → Nat → List (Term Symbol)) (states : List State)
    (child : State) (present : child ∈ states)
    (empty : ∀ size, classAt child size = []) (remaining : Nat) :
    go classAt states remaining = [] := by
  induction states generalizing remaining with
  | nil => cases present
  | cons current before ih =>
      rcases List.mem_cons.mp present with same | member
      · subst current
        simp [go, empty]
      · simp only [go]
        apply List.flatMap_eq_nil_iff.mpr
        intro left _
        rw [ih member left]
        rfl

/-- A transition with an empty child builds no candidate at any size. -/
theorem candidates_nil_of_child {State Symbol : Type}
    (classAt : State → Nat → List (Term Symbol)) (label : Symbol)
    (children : List State) (child : State) (present : child ∈ children)
    (empty : ∀ size, classAt child size = []) (size : Nat) :
    candidates classAt label children size = [] := by
  cases size with
  | zero => rfl
  | succ remaining =>
      simp only [candidates, go_nil_of_child classAt children.reverse child
        (List.mem_reverse.mpr present) empty, List.map_nil]

end MicroCFTA.SourceSizedCandidates
