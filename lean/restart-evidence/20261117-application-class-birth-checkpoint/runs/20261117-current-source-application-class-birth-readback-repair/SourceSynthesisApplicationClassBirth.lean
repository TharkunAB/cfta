import MicroCFTA.SourceSynthesisOwnChildTerminals
import MicroCFTA.SourcePruningEnumerationOwnInputShape

namespace MicroCFTA.SourceSynthesisApplicationClassBirth
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Input" => Node × List Suspended ×
  Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
set_option autoImplicit false

/- Note [Application class birth]
The actual source field certificate and physical arity select the application
constructor. They retain its complete guard. The observed cached own action
then fixes the allocated slots, ordered child buckets and endpoint cache.
The path list identifies each equality class before any child union runs.
The second class has the source Marker occurrences. The first and third
classes have the source Type occurrences. These names describe source
positions. They do not assert TypeIn or compatibility after later merges.
See the packet NOTES.md for the current-source provenance boundary.
-/

/-- An actual four-child source application allocates its three exact path classes. -/
theorem application_class_birth
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (before after : Cached) (symbol : Symbol) (staged : List Input)
    (residual : Option Constraint)
    (fields : SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge)
    (four : edge.children.length = 4) (storage : StorageValid before.core)
    (observed : SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
      some [((symbol, staged, residual), after)]) :
    let classes : EqualityNormalize.Constraints :=
      [[[0], [2, 0, 2]], [[1], [2, 0, 0]], [[2, 0, 1], [3, 0]]]
    let tries := EnumerationEquality.readClasses classes
    let start := before.core.counter
    let own := suspendedVars start tries
    SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, none) ∧
      symbol = literal "app" ∧ residual = none ∧
      after.core = suspendedState 3 before.core ∧
      after.core.counter = start + 3 ∧
      after.core.representatives = before.core.representatives ∧
      after.core.values = before.core.values ++ List.replicate 3 (.unenumerated none []) ∧
      (∀ offset, offset < 3 →
        after.core.values[start + offset]? = some (.unenumerated none []) ∧
        UnionFind.read after.core.representatives (start + offset) = .root 1) ∧
      (∀ left right, left < 3 → right < 3 →
        (UnionFind.SameClass after.core.representatives (start + left) (start + right) ↔
          left = right)) ∧
      own.map (fun sc => (sc.var, EqualityTrie.fromPathTrie sc.trie)) =
        [(start, [[0], [2, 0, 2]]),
         (start + 1, [[1], [2, 0, 0]]),
         (start + 2, [[2, 0, 1], [3, 0]])] ∧
      staged = (SourcePruningEnumerationEdgeInputs.children edge scs start tries).map
        (fun input => (input.1, input.2,
          SourcePruningEnumerationShallowChild.prepareChild
            (EnumGuard := Constraint) input.2 input.1)) ∧
      ∀ index incoming bucket action, staged[index]? = some (incoming, bucket, action) →
        bucket = descendScs index scs ++ descendScs index own
 := by
  dsimp only
  let classes : EqualityNormalize.Constraints :=
    [[[0], [2, 0, 2]], [[1], [2, 0, 0]], [[2, 0, 1], [3, 0]]]
  let tries := EnumerationEquality.readClasses classes
  let start := before.core.counter
  let own := suspendedVars start tries
  have sourceFields : edge.entry.key.symbol = literal "app" ∧
      edge.entry.key.constraint = SourceSynthesisGeneralizeSyntax.eqGuard
        [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]] := by
    cases fields with
    | annotated edge annotation guard children typed =>
        have impossible : (1 : Nat) = 4 := by
          simpa only [children, List.length_singleton] using four
        omega
    | application edge types marker function argument symbol guard children
        typesTyped markerTyped functionFields argumentFields =>
        exact ⟨symbol, guard⟩
    | filter edge goal candidates symbol guard children goalTyped candidateFields =>
        have impossible : (2 : Nat) = 4 := by
          simpa only [children, List.length_cons, List.length_nil] using four
        omega
  have projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint =
      some (tries, none) := by
    rw [sourceFields.2]
    exact SourceSynthesisOwnChildTerminals.application_projection
  have payload := SourcePruningEnumerationCachedOwn.prepare_inputs heap scs edge before after
    tries none (symbol, staged, residual) projected observed
  have scalars := SourcePruningEnumerationCachedOwn.prepare_scalars heap scs edge before after
    tries none (symbol, staged, residual) projected observed
  have symbolSame : symbol = edge.entry.key.symbol := congrArg Prod.fst payload
  have residualSame : residual = none := congrArg (fun result : Symbol × List Input × Option Constraint => result.2.2) payload
  have stagedSame : staged =
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries).map
        (fun input => (input.1, input.2,
          SourcePruningEnumerationShallowChild.prepareChild
            (EnumGuard := Constraint) input.2 input.1)) :=
    congrArg (fun result : Symbol × List Input × Option Constraint => result.2.1) payload
  have coreSame : after.core = suspendedState 3 before.core := scalars.2.1
  have counterSame : after.core.counter = start + 3 := scalars.2.2.1
  have forestSame : after.core.representatives = before.core.representatives := by
    rw [coreSame]
    exact EnumerationConstruction.suspended_forest 3 before.core
  have valuesSame : after.core.values =
      before.core.values ++ List.replicate 3 (.unenumerated none []) := by
    rw [coreSame]
    simp [suspendedState, allocated, List.replicate_succ, List.append_assoc]
  have fresh : ∀ offset, offset < 3 →
      after.core.values[start + offset]? = some (.unenumerated none []) ∧
      UnionFind.read after.core.representatives (start + offset) = .root 1 := by
    intro offset inside
    have outside : before.core.values.length ≤ start + offset := by
      rw [← storage.aligned]
      dsimp only [start]
      omega
    have difference : start + offset - before.core.values.length = offset := by
      rw [← storage.aligned]
      dsimp only [start]
      omega
    constructor
    · rw [valuesSame, List.getElem?_append_right outside, difference]
      exact List.getElem?_replicate_of_lt inside
    · rw [forestSame]
      unfold UnionFind.read
      rw [outside_forest before.core.representatives before.core.counter (start + offset)
        storage.forest (by dsimp only [start]; omega)]
      rfl
  have distinct : ∀ left right, left < 3 → right < 3 →
      (UnionFind.SameClass after.core.representatives (start + left) (start + right) ↔
        left = right) := by
    intro left right leftInside rightInside
    have roots := UnionFind.sameClass_iff_roots
      (UnionFind.Reaches.root (fresh left leftInside).2)
      (UnionFind.Reaches.root (fresh right rightInside).2)
    exact roots.trans (by omega)
  have pathReadback : own.map (fun sc => (sc.var, EqualityTrie.fromPathTrie sc.trie)) =
      [(start, [[0], [2, 0, 2]]),
       (start + 1, [[1], [2, 0, 0]]),
       (start + 2, [[2, 0, 1], [3, 0]])] := by
    cbv
  refine ⟨projected, symbolSame.trans sourceFields.1, residualSame, coreSame, counterSame,
    forestSame, valuesSame, fresh, distinct, pathReadback, stagedSame, ?_⟩
  intro index incoming bucket action input
  rw [stagedSame, SourcePruningEnumerationEdgeInputs.children, List.map_map,
    List.getElem?_map] at input
  obtain ⟨indexed, indexedStored, inputSame⟩ := Option.map_eq_some_iff.mp input
  rw [List.getElem?_zipIdx] at indexedStored
  obtain ⟨child, _childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
  simpa only [Function.comp_def] using
    (congrArg (fun result : Input => result.2.1) inputSame).symm

end MicroCFTA.SourceSynthesisApplicationClassBirth
