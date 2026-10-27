import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.InternedGuardedLanguage

/-!
# Ordered language evidence for actual selected-edge children

The input list uses the stored native children and their actual indices.
Structural retention and the parent semantic gates remain explicit.
-/
namespace MicroCFTA.SourcePruningEnumerationEdgeChildLanguage
open Language EnumerationState EnumerationCorrectness
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol

private theorem retained_bucket (incoming : Node) (bucket : List Suspended)
    (retained : (match incoming with | .node _ _ _ _ => True | _ => False) ∨
      bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    (match incoming with
      | .node _ _ _ _ => bucket
      | _ => if bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) then bucket else []) = bucket := by
  cases incoming <;> first
    | rfl
    | rcases retained with ordinary | hasTerminal | emptyBucket
      · cases ordinary
      · simp only [hasTerminal, ↓reduceIte]
      · simp only [emptyBucket, List.any_nil, Bool.false_eq_true, ↓reduceIte]

private theorem descend_append (index : Nat) (first second : List Suspended) :
    descendScs index (first ++ second) = descendScs index first ++ descendScs index second := by
  simp only [descendScs, EqualityTrie.descendScs, List.map_append, List.filter_append]

/-- Retained child buckets give the native forest and every indexed descended restriction. -/
theorem child_evidence
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (edge : EdgeValue Symbol Constraint)
    (scs : List Suspended) (start : Nat) (tries : List EqualityTrie.Trie)
    (fragments : List Fragment)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs start tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    (related : All₂ (fun (input : Node × List Suspended) (fragment : Fragment) =>
      InternedGuardedLanguage.meaning holds ambient input.1 (Fragments.fill assignment fragment) ∧
      ∀ sc ∈ (match input.1 with
        | .node _ _ _ _ => input.2
        | _ => if input.2.any (fun sc => EqualityTrie.isTerminal sc.trie) then input.2 else []),
        Suspended.Holds assignment (Fragments.fill assignment fragment) sc)
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries) fragments) :
    InternedGuardedLanguage.forest holds ambient edge.children
      (fragments.map (Fragments.fill assignment)) ∧
      ∀ index child, (fragments.map (Fragments.fill assignment))[index]? = some child →
        ∀ sc ∈ descendScs index (scs ++ suspendedVars start tries),
          Suspended.Holds assignment child sc := by
  constructor
  · have accepted := EnumerationSemantics.all₂_map_both Prod.fst (Fragments.fill assignment)
      _ (InternedGuardedLanguage.meaning holds ambient) (fun _ _ evidence => evidence.1)
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries) fragments related
    have inputValues : (SourcePruningEnumerationEdgeInputs.children edge scs start tries).map Prod.fst =
        edge.children := by
      simp only [SourcePruningEnumerationEdgeInputs.children, List.map_map]
      change edge.children.zipIdx.map Prod.fst = edge.children
      exact List.zipIdx_map_fst 0 edge.children
    apply (InternedGuardedLanguage.forest_all holds ambient edge.children _).mpr
    simpa only [inputValues] using accepted
  · intro index child found
    rw [List.getElem?_map] at found
    obtain ⟨fragment, stored, same⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨input, inputStored, evidence⟩ := EnumerationSemantics.all₂_get_right _
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries) fragments related index fragment stored
    have kept := retained_bucket input.1 input.2
      (retained input.1 input.2 (by simpa only [Prod.eta] using List.mem_of_getElem? inputStored))
    have bucketEvidence : ∀ sc ∈ input.2,
        Suspended.Holds assignment (Fragments.fill assignment fragment) sc := by
      rcases input with ⟨incoming, bucket⟩
      cases incoming <;> simpa only [kept] using evidence.2
    rw [SourcePruningEnumerationEdgeInputs.children, List.getElem?_map] at inputStored
    obtain ⟨indexed, indexedStored, inputSame⟩ := Option.map_eq_some_iff.mp inputStored
    have indexSame : indexed.2 = index := by
      rw [List.getElem?_zipIdx] at indexedStored
      obtain ⟨storedChild, _childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
      simp
    have bucketSame : descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars start tries) = input.2 :=
      congrArg Prod.snd inputSame
    rw [← bucketSame] at bucketEvidence
    simpa only [indexSame, ← descend_append, same] using bucketEvidence

/-- Valid parent tries and both arity gates turn child evidence into parent restrictions. -/
theorem restrictions_from_children
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (edge : EdgeValue Symbol Constraint)
    (scs : List Suspended) (start : Nat) (tries : List EqualityTrie.Trie)
    (fragments : List Fragment)
    (forest : InternedGuardedLanguage.forest holds ambient edge.children
      (fragments.map (Fragments.fill assignment)))
    (descendants : ∀ index child, (fragments.map (Fragments.fill assignment))[index]? = some child →
      ∀ sc ∈ descendScs index (scs ++ suspendedVars start tries), Suspended.Holds assignment child sc)
    (valid : ∀ trie ∈ tries, EqualityTrie.Valid trie)
    (freshArity : arityAllows edge.children.length (suspendedVars start tries) = true)
    (inheritedValid : EnumerationSemantics.ValidSuspended scs)
    (originalArity : arityAllows edge.children.length scs = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    (∀ trie ∈ tries,
      EqualityHolds (.node edge.entry.key.symbol (fragments.map (Fragments.fill assignment))) trie) ∧
      ∀ sc ∈ scs, Suspended.Holds assignment
        (.node edge.entry.key.symbol (fragments.map (Fragments.fill assignment))) sc := by
  have lengthSame : (fragments.map (Fragments.fill assignment)).length = edge.children.length :=
    ((InternedGuardedLanguage.forest_all holds ambient edge.children _).mp forest).length_eq.symm
  constructor
  · apply edge_equalities_from_children assignment edge.entry.key.symbol
      (fragments.map (Fragments.fill assignment)) tries start scs valid
      (by simpa only [lengthSame] using freshArity) descendants
  · apply suspended_descent_complete assignment edge.entry.key.symbol
      (fragments.map (Fragments.fill assignment)) scs inheritedValid
      (by simpa only [lengthSame] using originalArity)
    · intro sc member terminal
      exact False.elim ((List.any_eq_false.mp nonterminal sc member) terminal)
    · intro index child found sc member
      exact descendants index child found sc (descendScs_mono index scs
        (scs ++ suspendedVars start tries) (fun _ present => List.mem_append_left _ present) member)

end MicroCFTA.SourcePruningEnumerationEdgeChildLanguage
