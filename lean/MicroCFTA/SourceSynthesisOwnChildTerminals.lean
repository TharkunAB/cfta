import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.SourcePruningEnumerationConstraint

/-!
# Own terminal buckets at source Type fields

Application and filter equalities assign a terminal to each direct Type field.
The proof uses the normalized payload of the actual source guard projection.
It also uses the actual child-input list. The annotated variable row has no
own equality classes. This result does not cover its recursive Type child.
-/
namespace MicroCFTA.SourceSynthesisOwnChildTerminals
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceSynthesisGeneralizeSyntax (eqGuard)
open SourceSynthesisHereditaryProgramFields (EdgeFields)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Source application and filter rows place Type fields at these positions. -/
def TypeSlot (edge : EdgeValue Symbol Guard) (index : Nat) : Prop :=
  (edge.children.length = 4 ∧ (index = 0 ∨ index = 1)) ∨
    (edge.children.length = 2 ∧ index = 0)

private theorem stable_guard (input output : EqualityNormalize.Constraints)
    (prepared : EqualityNormalize.complete (EqualityNormalize.prepare input) = output)
    (stable : EqualityNormalize.congruenceStep output = some output) :
    eqGuard input = (⟨some output, .top⟩ : Guard) := by
  have positive : 0 < EqualityTermination.normalizationBound input := Nat.zero_lt_succ _
  unfold eqGuard EqualityNormalize.mkEqConstraints
  rw [prepared]
  cases bound : EqualityTermination.normalizationBound input with
  | zero => rw [bound] at positive; exact (Nat.not_lt_zero _ positive).elim
  | succ fuel =>
      simp only [EqualityNormalize.fixMaybe, stable, ite_true,
        SymbolicEqualityBridge.resultClasses]

/-- The literal application guard projects its actual canonical equality classes. -/
theorem application_projection :
    SourcePruningEnumerationConstraint.project
      (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]]) =
      some (EnumerationEquality.readClasses
        [[[0], [2, 0, 2]], [[1], [2, 0, 0]], [[2, 0, 1], [3, 0]]], none) := by
  have payload :
      eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]] =
        (⟨some [[[0], [2, 0, 2]], [[1], [2, 0, 0]], [[2, 0, 1], [3, 0]]], .top⟩ : Guard) := by
    apply stable_guard <;> cbv
  rw [payload]
  rfl

/-- The literal filter guard projects its actual canonical equality class. -/
theorem filter_projection :
    SourcePruningEnumerationConstraint.project (eqGuard [[[0], [1, 0]]]) =
      some (EnumerationEquality.readClasses [[[0], [1, 0]]], none) := by
  have payload : eqGuard [[[0], [1, 0]]] =
      (⟨some [[[0], [1, 0]]], .top⟩ : Guard) := by
    apply stable_guard <;> cbv
  rw [payload]
  rfl

private theorem any_descent (index : Nat) (scs : List Suspended) :
    (descendScs index scs).any (fun sc => EqualityTrie.isTerminal sc.trie) =
      scs.any (fun sc => EqualityTrie.isTerminal (EqualityTrie.pathTrieDescend sc.trie index)) := by
  simp only [descendScs, EqualityTrie.descendScs, List.any_filter, List.any_map, Function.comp_def]
  apply List.any_congr rfl
  intro sc
  cases EqualityTrie.pathTrieDescend sc.trie index <;> rfl

private theorem any_suspended (index start : Nat) (tries : List EqualityTrie.Trie) :
    (descendScs index (suspendedVars start tries)).any (fun sc => EqualityTrie.isTerminal sc.trie) =
      tries.any (fun trie => EqualityTrie.isTerminal (EqualityTrie.pathTrieDescend trie index)) := by
  rw [any_descent]
  induction tries generalizing start with
  | nil => rfl
  | cons trie rest ih =>
      simpa only [suspendedVars, List.any_cons] using congrArg
        (fun result => EqualityTrie.isTerminal (EqualityTrie.pathTrieDescend trie index) || result)
        (ih (start + 1))

/-- Actual source Type inputs contain an own terminal and retain the full bucket. -/
theorem type_input_retained
    {valid : Guard → Prop} {literal : String → Symbol}
    {edge : EdgeValue Symbol Guard} {index start : Nat} {scs : List Suspended}
    {tries : List EqualityTrie.Trie} {residual : Option Guard}
    {incoming : Value Symbol Guard} {bucket : List Suspended}
    (fields : EdgeFields valid literal edge) (slot : TypeSlot edge index)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint =
      some (tries, residual))
    (input : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket)) :
    bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∧
      (match incoming with
        | .node _ _ _ _ => bucket
        | _ => if bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) then bucket else []) = bucket := by
  have bucketSame : bucket =
      descendScs index scs ++ descendScs index (suspendedVars start tries) := by
    rw [SourcePruningEnumerationEdgeInputs.children, List.getElem?_map] at input
    obtain ⟨indexed, indexedStored, pairSame⟩ := Option.map_eq_some_iff.mp input
    rw [List.getElem?_zipIdx] at indexedStored
    obtain ⟨child, _childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
    simpa only [Nat.zero_add] using (congrArg Prod.snd pairSame).symm
  have ownTerminal : (descendScs index (suspendedVars start tries)).any
      (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
    cases fields with
    | annotated edge annotation guard children typed =>
        simp [TypeSlot, children] at slot
    | application edge types marker function argument symbol guard children
        typesTyped markerTyped functionFields argumentFields =>
        have indices : index = 0 ∨ index = 1 := by
          simpa [TypeSlot, children] using slot
        rw [guard, application_projection] at projected
        have triesSame : tries = EnumerationEquality.readClasses
            [[[0], [2, 0, 2]], [[1], [2, 0, 0]], [[2, 0, 1], [3, 0]]] :=
          (congrArg Prod.fst (Option.some.inj projected)).symm
        rw [triesSame, any_suspended]
        rcases indices with rfl | rfl <;> cbv
    | filter edge goal candidates symbol guard children goalTyped candidateFields =>
        have indexSame : index = 0 := by simpa [TypeSlot, children] using slot
        rw [guard, filter_projection] at projected
        have triesSame : tries = EnumerationEquality.readClasses [[[0], [1, 0]]] :=
          (congrArg Prod.fst (Option.some.inj projected)).symm
        rw [triesSame, any_suspended, indexSame]
        cbv
  have terminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
    rw [bucketSame, List.any_append, ownTerminal]
    simp
  refine ⟨terminal, ?_⟩
  cases incoming <;> simp only [terminal, ↓reduceIte]

end MicroCFTA.SourceSynthesisOwnChildTerminals
