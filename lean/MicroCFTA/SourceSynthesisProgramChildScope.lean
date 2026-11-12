import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourceSynthesisGuardRegions
import MicroCFTA.SourcePruningEnumerationPathTransport
import MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates

/-!
# Suspended equality scope at actual Program-child occurrences

The complete source row determines the child role and fixed guard.
The actual projected classes and indexed inputs determine the same bucket.
Inherited annotation paths do not enter a nonzero Program child.
Fresh own-class descents retain only the child annotation paths.
-/
namespace MicroCFTA.SourceSynthesisProgramChildScope
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisGuardRegions
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem annotation_tail (path : EqualityTrie.Path) (within : annotationRegion path) :
    ∃ tail, path = 0 :: tail := by
  obtain ⟨tail, same⟩ := within
  exact ⟨tail, same.symm⟩

private theorem inherited_empty (scs : List Suspended) (index : Nat) (nonzero : index ≠ 0)
    (inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) :
    descendScs index scs = [] := by
  change EqualityTrie.descendScs index scs = []
  unfold EqualityTrie.descendScs
  apply List.filter_eq_nil_iff.mpr
  intro sc member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
  have noPaths : EqualityTrie.fromPathTrie (EqualityTrie.pathTrieDescend original.trie index) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro path represented
    have originalPath := (EqualityTrie.descend_exact original.trie (inherited original included).1 index path).mp represented
    obtain ⟨tail, same⟩ := (inherited original included).2 (index :: path) originalPath
    exact nonzero (List.cons.inj same).1
  have empty := (EqualityTrie.empty_exact _
    (EqualityTrie.descend_valid original.trie (inherited original included).1 index)).mpr noPaths
  simp [empty]

private theorem projected_scope (constraint : Constraint)
    (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project constraint = some (tries, residual))
    (index : Nat)
    (scope : ∀ suffix, index :: suffix ∈ EqualityNormalize.members
      ((SourceCompactGuards.sourceEqualities constraint).getD []) → ∃ tail, suffix = 0 :: tail) :
    (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ trie ∈ tries, ∀ suffix, index :: suffix ∈ EqualityTrie.fromPathTrie trie →
        ∃ tail, suffix = 0 :: tail := by
  have checked := SourcePruningEnumerationConstraint.project_complete constraint cached
  cases source : SourceCompactGuards.sourceEqualities constraint with
  | none =>
      simp only [source] at checked
      rw [checked.1] at projected
      cases projected
  | some classes =>
      simp only [source] at checked
      have same : EnumerationEquality.readClasses classes = tries :=
        congrArg Prod.fst (Option.some.inj (checked.1.symm.trans projected))
      rw [← same]
      refine ⟨checked.2.1, ?_⟩
      intro trie member suffix represented
      obtain ⟨paths, included, rfl⟩ := List.mem_map.mp member
      have originalPath := (checked.2.2.1 paths included (index :: suffix)).mp represented
      apply scope suffix
      simp only [source, Option.getD_some, EqualityNormalize.members, List.mem_eraseDups]
      exact List.mem_flatten.mpr ⟨paths, included, originalPath⟩

private theorem descend_scope (scs : List Suspended) (index : Nat)
    (scope : ∀ sc ∈ scs, ∀ suffix, index :: suffix ∈ EqualityTrie.fromPathTrie sc.trie →
      ∃ tail, suffix = 0 :: tail) :
    ∀ sc ∈ descendScs index scs, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
      ∃ tail, path = 0 :: tail := by
  intro sc member path represented
  change sc ∈ EqualityTrie.descendScs index scs at member
  unfold EqualityTrie.descendScs at member
  obtain ⟨mapped, _retained⟩ := List.mem_filter.mp member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp mapped
  exact scope original included path
    (SourcePruningEnumerationPathTransport.descended_path_original original.trie index path represented)

/-- The same actual Program child has valid annotation-only suspended paths. -/
theorem program_child_scope
    (valid : Constraint → Prop) (edge : EdgeValue Symbol Constraint)
    (fields : SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge)
    (scs : List EnumerationState.Suspended) (start : Nat)
    (inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (index : Nat) (incoming : Node) (bucket : List EnumerationState.Suspended)
    (selected : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket))
    (programIndex :
      (edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
      (edge.entry.key.symbol = literal "filter" ∧ index = 1)) :
    SourceSynthesisHereditaryProgramFields.ValueFields valid literal incoming ∧
      EnumerationState.descendScs index scs = [] ∧
      bucket = EnumerationState.descendScs index (EnumerationCorrectness.suspendedVars start tries) ∧
      ∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
  have selectedMember := List.mem_of_getElem? selected
  rw [SourcePruningEnumerationEdgeInputs.children, List.getElem?_map] at selected
  obtain ⟨indexed, indexedStored, inputSame⟩ := Option.map_eq_some_iff.mp selected
  have indexSame : indexed.2 = index := by
    rw [List.getElem?_zipIdx] at indexedStored
    obtain ⟨storedChild, _childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
    simp
  have childStored : edge.children[index]? = some incoming := by
    rw [List.getElem?_zipIdx] at indexedStored
    obtain ⟨storedChild, childStored, pairSame⟩ := Option.map_eq_some_iff.mp indexedStored
    have childSame : storedChild = incoming :=
      (congrArg Prod.fst pairSame).trans (congrArg Prod.fst inputSame)
    simpa only [childSame] using childStored
  have bucketSame : descendScs index scs ++ descendScs index (suspendedVars start tries) = bucket := by
    simpa only [indexSame] using congrArg Prod.snd inputSame
  have nonzero : index ≠ 0 := by
    rcases programIndex with ⟨_symbol, rfl | rfl⟩ | ⟨_symbol, rfl⟩ <;> decide
  have inheritedEmpty := inherited_empty scs index nonzero inherited
  have ownBucket : bucket = descendScs index (suspendedVars start tries) := by
    rw [← bucketSame, inheritedEmpty, List.nil_append]
  have rowScope : ValueFields valid literal incoming ∧
      SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities ∧
      ∀ suffix, index :: suffix ∈ EqualityNormalize.members
        ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []) →
        ∃ tail, suffix = 0 :: tail := by
    cases fields with
    | annotated edge annotation _guard children _typed =>
        rcases programIndex with ⟨_symbol, rfl | rfl⟩ | ⟨_symbol, rfl⟩ <;>
          simp [children] at childStored
    | application edge types marker function argument symbol guard children _typesTyped _markerTyped
        functionFields argumentFields =>
        have position : index = 2 ∨ index = 3 := by
          rcases programIndex with position | ⟨other, _position⟩
          · exact position.2
          · have names : ("app" : String) = "filter" :=
              congrArg Prod.fst (symbol.symm.trans other)
            exact False.elim ((by decide : ("app" : String) ≠ "filter") names)
        refine ⟨?_, ?_, ?_⟩
        · rcases position with rfl | rfl
          · have same : function = incoming := Option.some.inj (by
              simpa only [children, List.getElem?_cons_succ, List.getElem?_cons_zero] using childStored)
            exact same ▸ functionFields
          · have same : argument = incoming := Option.some.inj (by
              simpa only [children, List.getElem?_cons_succ, List.getElem?_cons_zero] using childStored)
            exact same ▸ argumentFields
        · rw [guard, SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
          exact SourceEqualityGuardReadback.normalize_cached _
        · intro suffix member
          have region : applicationRegion (index :: suffix) :=
            (application_guard_endpoints .empty .empty .empty "app" _
              [.empty, SourceSynthesisTypeSyntax.arrowMarker top, .empty, .empty] rfl).2 _
                (by simpa only [guard] using member)
          rcases position with rfl | rfl
          · exact annotation_tail suffix ((application_descend_function suffix).mp region)
          · exact annotation_tail suffix ((application_descend_argument suffix).mp region)
    | filter edge goal candidates symbol guard children _goalTyped candidateFields =>
        have position : index = 1 := by
          rcases programIndex with ⟨other, _position⟩ | position
          · have names : ("filter" : String) = "app" :=
              congrArg Prod.fst (symbol.symm.trans other)
            exact False.elim ((by decide : ("filter" : String) ≠ "app") names)
          · exact position.2
        refine ⟨?_, ?_, ?_⟩
        · have same : candidates = incoming := Option.some.inj (by
            simpa only [children, position, List.getElem?_cons_succ, List.getElem?_cons_zero] using childStored)
          exact same ▸ candidateFields
        · rw [guard, SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
          exact SourceEqualityGuardReadback.normalize_cached _
        · intro suffix member
          have region : filterRegion (1 :: suffix) :=
            (filter_guard_endpoints .empty .empty "filter" _ [.empty, .empty] rfl).2 _
              (by simpa only [guard, position] using member)
          exact annotation_tail suffix ((filter_descend_program suffix).mp region)
  obtain ⟨projectedValid, projectedScope⟩ := projected_scope edge.entry.key.constraint rowScope.2.1
    tries residual projected index rowScope.2.2
  have bucketValid := SourcePruningEnumerationOrdinarySemanticGates.children_valid edge scs start tries
    (fun sc member => (inherited sc member).1) projectedValid incoming bucket selectedMember
  have ownScope : ∀ sc ∈ suspendedVars start tries, ∀ suffix,
      index :: suffix ∈ EqualityTrie.fromPathTrie sc.trie → ∃ tail, suffix = 0 :: tail := by
    intro sc member suffix represented
    have included : sc.trie ∈ tries := by
      rw [← suspendedVars_tries start tries]
      exact List.mem_map.mpr ⟨sc, member, rfl⟩
    exact projectedScope sc.trie included suffix represented
  refine ⟨rowScope.1, inheritedEmpty, ownBucket, ?_⟩
  intro sc member
  exact ⟨bucketValid sc member, descend_scope _ index ownScope sc (ownBucket ▸ member)⟩

end MicroCFTA.SourceSynthesisProgramChildScope
