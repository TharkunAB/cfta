import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.EnumerationProgress
import MicroCFTA.InternedGuardedLanguage

/-!
# Parent classes are separate from accepted proper child restrictions

A finite parent cannot occur inside one of its children. Canonical nonempty
child tries make each suspended child obligation name an actual subtree.
-/
namespace MicroCFTA.SourcePruningEnumerationParentChildSeparation
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics
open EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint

private theorem related_member {α β : Type} (relation : α → β → Prop)
    (left : List α) (right : List β) (related : All₂ relation left right)
    (input : α) (member : input ∈ left) :
    ∃ output ∈ right, relation input output := by
  induction related generalizing input with
  | nil => simp at member
  | cons head _tail ih =>
      rcases List.mem_cons.mp member with rfl | present
      · exact ⟨_, by simp, head⟩
      · obtain ⟨output, outputMember, evidence⟩ := ih input present
        exact ⟨output, List.mem_cons_of_mem _ outputMember, evidence⟩

/-- A real child bucket with actual paths cannot refer to the parent's equality class. -/
theorem proper_child_avoids_parent {Guard : Type}
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (before : EnumerationState.State Symbol Guard) (assignment : Nat → Term Symbol)
    (parent : Nat) (symbol : Symbol) (terms : List (Term Symbol)) (child : Term Symbol)
    (bucket : List Suspended)
    (satisfied : Satisfies language meaning assignment before)
    (parentValue : assignment parent = .node symbol terms)
    (childMember : child ∈ terms) (proper : ProperInputs bucket)
    (held : ∀ sc ∈ bucket, Suspended.Holds assignment child sc) :
    Avoids before.representatives parent bucket := by
  intro sc member sameClass
  have valid := (proper sc member).1
  have notEmpty : sc.trie ≠ .empty := by
    intro same
    have live := (proper sc member).2
    rw [same] at live
    cases live
  obtain ⟨path, present⟩ := EqualityTrie.valid_has_path sc.trie valid notEmpty
  have found := held sc member path present
  have equal : assignment parent = assignment sc.var := satisfied.1.1 parent sc.var sameClass
  rw [← equal, parentValue] at found
  have bound := atPath_height_bound child (.node symbol terms) path found
  have childBound := height_le_forestHeight terms child childMember
  simp only [Term.height, forestHeight] at bound childBound
  omega

/-- Actual selected-edge descents have real paths and avoid the modeled parent class. -/
theorem edge_children_avoid_parent {Guard : Type}
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (before : EnumerationState.State Symbol Guard) (assignment : Nat → Term Symbol)
    (parent : Nat) (edge : EdgeValue Symbol Constraint) (terms : List (Term Symbol))
    (scs : List Suspended) (start : Nat) (tries : List EqualityTrie.Trie)
    (satisfied : Satisfies language meaning assignment before)
    (parentValue : assignment parent = .node edge.entry.key.symbol terms)
    (canonical : ValidSuspended scs)
    (validOwn : ∀ trie ∈ tries, EqualityTrie.Valid trie)
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (models : All₂ (fun input child =>
      InternedGuardedLanguage.meaning holds ambient input.1 child ∧
      ∀ sc ∈ input.2, Suspended.Holds assignment child sc)
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries) terms) :
    ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs start tries →
      Avoids before.representatives parent bucket := by
  have freshValid : ValidSuspended (suspendedVars start tries) := by
    intro sc member
    apply validOwn sc.trie
    rw [← suspendedVars_tries start tries]
    exact List.mem_map.mpr ⟨sc, member, rfl⟩
  intro incoming bucket member
  obtain ⟨child, childMember, evidence⟩ := related_member _ _ _ models (incoming, bucket) member
  apply proper_child_avoids_parent language meaning before assignment parent edge.entry.key.symbol terms
    child bucket satisfied parentValue childMember ?_ evidence.2
  obtain ⟨indexed, _indexedMember, same⟩ := List.mem_map.mp member
  cases same
  intro sc present
  rcases List.mem_append.mp present with old | fresh
  · exact descend_proper scs indexed.2 canonical sc old
  · exact descend_proper (suspendedVars start tries) indexed.2 freshValid sc fresh

/-- The actual stored parent and canonical state supply inherited trie validity. -/
theorem stored_edge_children_avoid_parent {Guard : Type}
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (before : EnumerationState.State Symbol Guard) (assignment : Nat → Term Symbol)
    (parent handle : Nat) (edge : EdgeValue Symbol Constraint) (terms : List (Term Symbol))
    (scs : List Suspended) (start : Nat) (tries : List EqualityTrie.Trie)
    (satisfied : Satisfies language meaning assignment before)
    (parentValue : assignment parent = .node edge.entry.key.symbol terms)
    (canonical : EnumerationValidity.Canonical before)
    (stored : before.values[parent]? = some (.unenumerated (some handle) scs))
    (validOwn : ∀ trie ∈ tries, EqualityTrie.Valid trie)
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (models : All₂ (fun input child =>
      InternedGuardedLanguage.meaning holds ambient input.1 child ∧
      ∀ sc ∈ input.2, Suspended.Holds assignment child sc)
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries) terms) :
    ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs start tries →
      Avoids before.representatives parent bucket := by
  have valid : ValidSuspended scs := canonical _ (List.mem_of_getElem? stored)
  exact edge_children_avoid_parent language meaning before assignment parent edge terms scs start tries
    satisfied parentValue valid validOwn holds ambient models

end MicroCFTA.SourcePruningEnumerationParentChildSeparation
