import MicroCFTA.SourceEqualityPhysicalPayload

/-!
# Actual physical equality descent for the inherited source caller

The source descends each original trie, drops trivial suffix classes with
its structural two-path test, reconstructs the path set, and sorts retained
records by that set. Empty and contradictory payloads keep their source cases.
No normalization or whole-child language law replaces this descent.
-/
namespace MicroCFTA.SourceEqualityDescend
open Language EqualityNormalize EqualityTrie SourceEqualityClassOrder

/-- Actual class rebuilding reads the lazy ascending set from the descended trie. -/
def fromTrie (trie : Trie) : Record := ⟨trie, fromPathTrie trie⟩

/-- The actual source helper retains a descended class only when two suffix paths remain. -/
def record (index : Nat) (original : Record) : Option Record :=
  let trie := pathTrieDescend original.trie index
  if EqualitySaturation.pathTrieHasAtLeastTwoPaths trie then some (fromTrie trie) else none

/-- Source descent sorts retained classes by ascending path sets, with literal empty and singleton cases. -/
def records (index : Nat) (originals : List Record) : List Record :=
  let descended := originals.filterMap (record index)
  match descended with
  | [] => []
  | [single] => [single]
  | others => SourceListSort.sortBy (fun first second => compare first.paths second.paths) others

/-- Contradiction absorbs descent; an empty physical constraint returns immediately. -/
def descend : SourceEqualityPrecheck.Constraint → Nat → SourceEqualityPrecheck.Constraint
  | none, _ => none
  | some [], _ => some []
  | some originals, index => some (records index originals)

/-- Physical inherited payloads have coherent ascending tries and nontrivial classes. -/
def WellFormed (input : SourceEqualityPrecheck.Constraint) : Prop :=
  ∀ originals, input = some originals → ∀ original ∈ originals,
    Coherent original ∧ Ascending original.trie ∧ Nontrivial original.paths

/-- Ascending valid trie enumeration already has the canonical source path-set order. -/
theorem canonical_fromTrie (trie : Trie) (valid : Valid trie) (ascending : Ascending trie) :
    canonicalClass (fromPathTrie trie) = fromPathTrie trie := by
  have unique := supported_nodup _ (fromPathTrie_supported trie valid)
  have perm : (canonicalClass (fromPathTrie trie)).Perm (fromPathTrie trie) :=
    (List.perm_ext_iff_of_nodup (canonicalClass_nodup _) unique).mpr (fun path => mem_canonicalClass path _)
  exact perm.eq_of_pairwise (fun _ _ _ _ first second => List.le_antisymm first second)
    (canonicalClass_ordered _) ((fromPathTrie_increasing trie ascending).imp (fun before => List.le_of_lt before))

/-- Literal source trie reconstruction derives every physical class field invariant. -/
theorem fromTrie_coherent (trie : Trie) (valid : Valid trie) (ascending : Ascending trie) : Coherent (fromTrie trie) :=
  ⟨valid, canonical_fromTrie trie valid ascending, fun _ => Iff.rfl⟩

/-- Every actual successfully constructed class record has an ascending trie. -/
theorem recordOf_ascending (paths : Class) (output : Record) (built : recordOf paths = some output) : Ascending output.trie := by
  cases found : toPathTrie paths.eraseDups with
  | none => simp [recordOf, found] at built
  | some trie =>
      have same : output = ⟨trie, canonicalClass paths⟩ := by simpa only [recordOf, found, Option.map_some, Option.some.injEq] using built.symm
      rw [same]
      exact build_ascending _ _ _ found

/-- Successful physical payload construction derives ascending tries without an added input contract. -/
theorem recordsOf_ascending (classes : Constraints) (outputs : List Record) (built : recordsOf classes = some outputs) :
    ∀ output ∈ outputs, Ascending output.trie := by
  induction classes generalizing outputs with
  | nil => cases built; simp
  | cons first rest ih =>
      cases head : recordOf first with
      | none => simp [recordsOf, head] at built
      | some output =>
          cases tail : recordsOf rest with
          | none => simp [recordsOf, head, tail] at built
          | some remaining =>
              have same : output :: remaining = outputs := by simpa [recordsOf, head, tail] using built
              subst outputs
              intro current member
              rcases List.mem_cons.mp member with rfl | member
              · exact recordOf_ascending first current head
              · exact ih remaining tail current member

/-- Actual source sorting changes no retained class occurrence. -/
theorem records_perm (index : Nat) (originals : List Record) :
    (records index originals).Perm (originals.filterMap (record index)) := by
  dsimp only [records]
  split
  · simp_all
  · simp_all
  · exact SourceListSort.sortBy_perm _ _

/-- The actual helper returns precisely the same-child suffix pairs of one original class. -/
theorem record_pairs (index : Nat) (original : Record) (coherent : Coherent original) (output : Record)
    (found : record index original = some output) :
    ∀ suffix, suffix ∈ output.paths ↔ index :: suffix ∈ original.paths := by
  dsimp only [record] at found
  split at found
  · have same : fromTrie (pathTrieDescend original.trie index) = output := Option.some.inj found
    rw [← same]
    exact fun suffix => (descend_exact original.trie coherent.1 index suffix).trans (coherent.2.2 _)
  · cases found

/-- Every kept descended record derives coherent fields, ascending maps, and nontrivial suffix paths. -/
theorem record_wellFormed (index : Nat) (original : Record) (coherent : Coherent original) (ascending : Ascending original.trie)
    (output : Record) (found : record index original = some output) :
    Coherent output ∧ Ascending output.trie ∧ Nontrivial output.paths := by
  dsimp only [record] at found
  split at found
  · rename_i kept
    have same : fromTrie (pathTrieDescend original.trie index) = output := Option.some.inj found
    rw [← same]
    have valid := descend_valid original.trie coherent.1 index
    have sorted := descend_ascending original.trie ascending index
    exact ⟨fromTrie_coherent _ valid sorted, sorted, (EqualitySaturation.pathTrieHasAtLeastTwoPaths_nontrivial _ valid).mp kept⟩
  · cases found

/-- Descent preserves the actual physical inherited-payload invariant. -/
theorem descend_wellFormed (input : SourceEqualityPrecheck.Constraint) (wellFormed : WellFormed input) (index : Nat) :
    WellFormed (descend input index) := by
  cases input with
  | none => simp [descend, WellFormed]
  | some originals =>
      cases originals with
      | nil => simp [descend, WellFormed]
      | cons first rest =>
          intro outputs same output member
          have identical : records index (first :: rest) = outputs := Option.some.inj same
          rw [← identical] at member
          obtain ⟨original, included, found⟩ := List.mem_filterMap.mp ((records_perm index (first :: rest)).mem_iff.mp member)
          have valid := wellFormed (first :: rest) rfl original included
          exact record_wellFormed index original valid.1 valid.2.1 output found

/-- Physical descent denotes exactly all surviving same-child equality pairs. -/
theorem descend_exact (originals : List Record) (coherent : ∀ original ∈ originals, Coherent original) (index : Nat) (term : Term Symbol) :
    SourceEqualityPrecheck.Sat term (descend (some originals) index) ↔
      ∀ original ∈ originals, ∀ left, index :: left ∈ original.paths → ∀ right, index :: right ∈ original.paths →
        left ≠ right → PathsEqual term left right := by
  have sat : SourceEqualityPrecheck.Sat term (descend (some originals) index) ↔
      Satisfies term ((records index originals).map Record.paths) := by cases originals <;> rfl
  rw [sat]
  constructor
  · intro satisfied original member left leftMember right rightMember different
    have leftSuffix := (EqualityTrie.descend_exact original.trie (coherent original member).1 index left).mpr ((coherent original member).2.2 _ |>.mpr leftMember)
    have rightSuffix := (EqualityTrie.descend_exact original.trie (coherent original member).1 index right).mpr ((coherent original member).2.2 _ |>.mpr rightMember)
    have keep := (EqualitySaturation.pathTrieHasAtLeastTwoPaths_nontrivial _ (descend_valid original.trie (coherent original member).1 index)).mpr
      ⟨left, leftSuffix, right, rightSuffix, different⟩
    have found : record index original = some (fromTrie (pathTrieDescend original.trie index)) := by simp only [record, keep, ite_true]
    have selected := (records_perm index originals).mem_iff.mpr (List.mem_filterMap.mpr ⟨original, member, found⟩)
    exact satisfied _ (List.mem_map.mpr ⟨_, selected, rfl⟩) left leftSuffix right rightSuffix different
  · intro satisfied paths member left leftMember right rightMember different
    obtain ⟨output, included, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, originalMember, found⟩ := List.mem_filterMap.mp ((records_perm index originals).mem_iff.mp included)
    have pairs := record_pairs index original (coherent original originalMember) output found
    exact satisfied original originalMember left ((pairs left).mp leftMember) right ((pairs right).mp rightMember) different

/-- A satisfied parent physical constraint supplies its actual descended constraint to every existing child. -/
theorem descend_sound (input : SourceEqualityPrecheck.Constraint) (wellFormed : WellFormed input)
    (symbol : Symbol) (children : List (Term Symbol)) (index : Nat) (child : Term Symbol) (found : children[index]? = some child)
    (satisfied : SourceEqualityPrecheck.Sat (.node symbol children) input) : SourceEqualityPrecheck.Sat child (descend input index) := by
  cases input with
  | none => exact False.elim satisfied
  | some originals =>
      rw [descend_exact originals (fun original member => (wellFormed originals rfl original member).1)]
      intro original member left leftMember right rightMember different
      exact (pathsEqual_child symbol children index child found left right).mp
        (satisfied original.paths (List.mem_map.mpr ⟨original, member, rfl⟩) (index :: left) leftMember (index :: right) rightMember (by simp [different]))

end MicroCFTA.SourceEqualityDescend
