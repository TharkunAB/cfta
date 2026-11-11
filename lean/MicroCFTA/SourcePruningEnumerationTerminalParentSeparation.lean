import MicroCFTA.SourcePruningEnumerationParentChildSeparation

/-!
# Terminal child restrictions avoid the modeled parent class

Terminal tries supply valid nonempty paths without a canonicality premise.
The literal partition selects those restrictions from the same child bucket.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalParentSeparation
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics
open EnumerationProgress
local notation "Symbol" => SourcePruningTemplates.Symbol

/-- Held terminal restrictions of a strict child cannot name its parent class. -/
theorem terminal_child_avoids_parent {Guard : Type}
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (before : EnumerationState.State Symbol Guard) (assignment : Nat → Term Symbol)
    (parent : Nat) (symbol : Symbol) (terms : List (Term Symbol)) (child : Term Symbol)
    (bucket : List Suspended)
    (satisfied : Satisfies language meaning assignment before)
    (parentValue : assignment parent = .node symbol terms)
    (childMember : child ∈ terms)
    (terminal : ∀ sc ∈ bucket, EqualityTrie.isTerminal sc.trie = true)
    (held : ∀ sc ∈ bucket, Suspended.Holds assignment child sc) :
    Avoids before.representatives parent bucket := by
  have proper : ProperInputs bucket := by
    intro sc member
    have atRoot := terminal sc member
    cases shape : sc.trie with
    | empty =>
        simp only [shape, EqualityTrie.isTerminal, Bool.false_eq_true] at atRoot
    | terminal =>
        exact ⟨by simp only [EqualityTrie.Valid],
          by simp only [EqualityTrie.isEmpty]⟩
    | branch children =>
        simp only [shape, EqualityTrie.isTerminal, Bool.false_eq_true] at atRoot
  exact SourcePruningEnumerationParentChildSeparation.proper_child_avoids_parent
    language meaning before assignment parent symbol terms child bucket satisfied parentValue
    childMember proper held

/-- The exact terminal partition inherits avoidance from the same full child model. -/
theorem partition_child_avoids_parent {Guard : Type}
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (before : EnumerationState.State Symbol Guard) (assignment : Nat → Term Symbol)
    (parent : Nat) (symbol : Symbol) (terms : List (Term Symbol)) (child : Term Symbol)
    (bucket : List Suspended) (first : Suspended) (rest descendants : List Suspended)
    (satisfied : Satisfies language meaning assignment before)
    (parentValue : assignment parent = .node symbol terms)
    (childMember : child ∈ terms)
    (partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants))
    (held : ∀ sc ∈ bucket, Suspended.Holds assignment child sc) :
    Avoids before.representatives parent (first :: rest) := by
  have terminalPart : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
    simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
  have subset : ∀ sc ∈ first :: rest, sc ∈ bucket := by
    intro sc member
    rw [← terminalPart] at member
    exact (List.mem_filter.mp member).1
  have terminal : ∀ sc ∈ first :: rest, EqualityTrie.isTerminal sc.trie = true := by
    intro sc member
    rw [← terminalPart] at member
    exact (List.mem_filter.mp member).2
  exact terminal_child_avoids_parent language meaning before assignment parent symbol terms
    child (first :: rest) satisfied parentValue childMember terminal
    (fun sc member => held sc (subset sc member))

end MicroCFTA.SourcePruningEnumerationTerminalParentSeparation
