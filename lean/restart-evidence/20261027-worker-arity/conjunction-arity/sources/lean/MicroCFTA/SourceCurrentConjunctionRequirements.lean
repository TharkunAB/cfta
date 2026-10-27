import MicroCFTA.SourceCurrentConjunctionCompletionReads
import MicroCFTA.SourceCurrentConjunctionMap
import MicroCFTA.SourceEmptinessKeys
import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Actual requirements of one current conjunction tuple

The graph emits child columns before equality classes. Each class projects
its original forests in row-major path order at the returned constructor
heap. Canonicalization uses the literal finite identity-map fold.

This is a chosen sequential resident schedule. It does not establish GHC
forcing order. Equality accessor and combination allocation occur before
this graph and have separate receipts.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirements
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionCompletionReads (Effects Projections jobs Inputs)
open InternedGuardedLanguage (meaning)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap

/-- The empty-node shortcut excludes this fallback from every resident map key. -/
def key (value : Value Symbol Guard) : Int := (SourceEmptinessKeys.key value).getD 0

/-- Test only the source empty constructor before reading any identity map. -/
def isEmpty : Value Symbol Guard → Bool
  | .empty => true
  | _ => false

/-- The constructor test is exactly membership of EmptyNode. -/
theorem any_empty (nodes : List (Value Symbol Guard)) : nodes.any isEmpty = true ↔ .empty ∈ nodes := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨value, member, empty⟩
    cases value <;> simp_all [isEmpty]
  · intro member
    exact ⟨.empty, member, rfl⟩

/-- The source canonical conjunction keeps one value per identity in ascending order. -/
def canonical (nodes : List (Value Symbol Guard)) : List (Value Symbol Guard) :=
  if nodes.any isEmpty then [.empty] else SourceCurrentConjunctionMap.elems key nodes

/-- The executable constructor test gives the literal source map conjunction. -/
theorem canonical_map [DecidableEq (Value Symbol Guard)] (nodes : List (Value Symbol Guard)) :
    canonical nodes = SourceCurrentConjunctionMap.conjunction .empty key nodes := by
  simp only [canonical, SourceCurrentConjunctionMap.conjunction, any_empty]

private theorem key_some (value : Value Symbol Guard) (closed : value.free = []) (nonempty : value ≠ .empty) :
    SourceEmptinessKeys.key value = some (key value) := by
  obtain ⟨entry, field⟩ := SourceEmptinessKeys.entry_of_closed value closed nonempty
  have raw := SourceEmptinessKeys.rawKey_of_entry value entry field
  simp only [SourceEmptinessKeys.key, raw, Option.map_some, key, Option.getD_some]

/-- Common-heap coherence derives exact map readback on the actual closed input list. -/
theorem canonical_exact [DecidableEq (Value Symbol Guard)] (nodes : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (semantic : SemanticReady heap) (available : Values heap nodes) (closed : ClosedValues nodes) :
    canonical nodes = SourceCurrentConjunctionEmptinessRows.conjunction .empty key nodes := by
  classical
  rw [canonical_map]
  by_cases impossible : (.empty : Value Symbol Guard) ∈ nodes
  · simp [SourceCurrentConjunctionMap.conjunction, SourceCurrentConjunctionEmptinessRows.conjunction, impossible]
  · simp only [SourceCurrentConjunctionMap.conjunction, SourceCurrentConjunctionEmptinessRows.conjunction,
      impossible, ite_false]
    apply SourceCurrentConjunctionMap.elems_exact
    intro left leftIn right rightIn same
    have first := key_some left (closed left leftIn) (fun equal => impossible (equal ▸ leftIn))
    have second := key_some right (closed right rightIn) (fun equal => impossible (equal ▸ rightIn))
    exact SourceEmptinessKeys.key_injective heap semantic.ready.semantic.1.normal.facts.coherent
      left right (available left leftIn) (available right rightIn) (closed left leftIn) (closed right rightIn)
      (first.trans ((congrArg some same).trans second.symm))

/-- Canonical requirements retain only available closed original records. -/
theorem canonical_values (nodes : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (semantic : SemanticReady heap) (available : Values heap nodes) (closed : ClosedValues nodes) :
    Values heap (canonical nodes) ∧ ClosedValues (canonical nodes) := by
  classical
  rw [canonical_exact nodes heap semantic available closed]
  by_cases impossible : (.empty : Value Symbol Guard) ∈ nodes
  · simp only [SourceCurrentConjunctionEmptinessRows.conjunction, impossible, ite_true]
    constructor
    · intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact empty_available heap
    · intro value member
      have same := List.mem_singleton.mp member
      subst value
      rfl
  · simp only [SourceCurrentConjunctionEmptinessRows.conjunction, impossible, ite_false]
    exact ⟨fun value member => available value (List.mem_eraseDups.mp (List.mem_mergeSort.mp member)),
      fun value member => closed value (List.mem_eraseDups.mp (List.mem_mergeSort.mp member))⟩

/-- Canonicalization preserves common-term acceptance on actual closed resident inputs. -/
theorem canonical_accepts (nodes : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (semantic : SemanticReady heap) (available : Values heap nodes) (closed : ClosedValues nodes)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    SourceCurrentConjunctionEmptinessRows.Accepts (meaning holds ambient) (canonical nodes) term ↔
      SourceCurrentConjunctionEmptinessRows.Accepts (meaning holds ambient) nodes term := by
  classical
  rw [canonical_exact nodes heap semantic available closed]
  exact SourceCurrentConjunctionEmptinessRows.conjunction_exact (Value.empty : Value Symbol Guard) key (meaning holds ambient)
    (fun term => (InternedGuardedLanguage.laws holds ambient).empty term) nodes term

/-- The first edge supplies the common arity of a literal nonempty tuple. -/
def arity (tuple : List (EdgeValue Symbol Guard)) : Nat :=
  ((tuple.head?).map (fun edge => edge.children.length)).getD 0

/-- Every child column precedes every class requirement. -/
def columns (tuple : List (EdgeValue Symbol Guard)) : List (List (Value Symbol Guard)) :=
  MergedAlternativesGroups.columns (tuple.map EdgeValue.children) (arity tuple)

/-- The source tuple filter supplies the same arity at each actual edge occurrence. -/
def SameArity (tuple : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ tuple, edge.children.length = arity tuple

/-- Each class retains its actual projection results and the next exact heap. -/
inductive ClassRequirements [DecidableEq (EdgeKey Symbol Guard)]
    (forests : List (List (Value Symbol Guard))) :
    Constraints → State Symbol Guard → List (List (Value Symbol Guard)) → State Symbol Guard → Prop where
  | nil : ClassRequirements forests [] state [] state
  | cons (first : Projections (jobs forests paths) before projected middle)
      (rest : ClassRequirements forests classes middle requirements after) :
      ClassRequirements forests (paths :: classes) before (canonical projected :: requirements) after

/-- A literal tuple first keeps child columns, then demands its class requirements. -/
inductive Requirements [DecidableEq (EdgeKey Symbol Guard)]
    (tuple : List (EdgeValue Symbol Guard)) (classes : Constraints) :
    State Symbol Guard → List (List (Value Symbol Guard)) → State Symbol Guard → Prop where
  | run (sameArity : SameArity tuple)
      (actual : ClassRequirements (tuple.map EdgeValue.children) classes before requirements after) :
      Requirements tuple classes before ((columns tuple).map canonical ++ requirements) after

/-- All stored requirements have closed available operands at the actual current heap. -/
def RowsReady (heap : State Symbol Guard) (rows : List (List (Value Symbol Guard))) : Prop :=
  ∀ row ∈ rows, Values heap row ∧ ClosedValues row

/-- A class list retains its exact number of requirements and their multiplicity. -/
theorem ClassRequirements.length [DecidableEq (EdgeKey Symbol Guard)]
    {forests : List (List (Value Symbol Guard))} {classes : Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : ClassRequirements forests classes before requirements after) : requirements.length = classes.length := by
  induction actual with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

/-- Actual finite class projections derive every output record and heap invariant. -/
theorem ClassRequirements.verified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {forests : List (List (Value Symbol Guard))} {classes : Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : ClassRequirements forests classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (inputs : RowsReady before forests) : Effects annotation before after ∧ RowsReady after requirements := by
  induction actual with
  | nil => exact ⟨⟨pure_keeps _ semantic.ready, semantic, costs, fields⟩, by simp [RowsReady]⟩
  | @cons paths before projected middle classes requirements after first rest ih =>
      have own := first.verified annotation semantic costs fields
        (SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
          (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2))
      have canonical := canonical_values projected middle own.1.semantic own.2.1 own.2.2
      have later := ih own.1.semantic own.1.costs own.1.annotations
        (fun forest member => ⟨fun child included => own.1.keeps.available child ((inputs forest member).1 child included),
          (inputs forest member).2⟩)
      refine ⟨⟨own.1.keeps.trans later.1.keeps, later.1.semantic, later.1.costs, later.1.annotations⟩, ?_⟩
      intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨fun child included => later.1.keeps.available child (canonical.1 child included), canonical.2⟩
      · exact later.2 row member

/-- Every finite class list completes from actual closed available original forests. -/
theorem classes_complete [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (forests : List (List (Value Symbol Guard))) (classes : Constraints)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before) (inputs : RowsReady before forests) :
    ∃ requirements after, ClassRequirements forests classes before requirements after ∧
      Effects annotation before after ∧ RowsReady after requirements := by
  induction classes generalizing before with
  | nil => exact ⟨[], before, .nil, ⟨pure_keeps _ semantic.ready, semantic, costs, fields⟩, by simp [RowsReady]⟩
  | cons paths classes ih =>
      obtain ⟨projected, middle, first, own, _, _⟩ :=
        SourceCurrentConjunctionCompletionReads.projections_complete annotation (jobs forests paths) before semantic costs fields
          (SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
            (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2))
      obtain ⟨requirements, after, rest, _, _⟩ := ih middle own.semantic own.costs own.annotations
        (fun forest member => ⟨fun child included => own.keeps.available child ((inputs forest member).1 child included),
          (inputs forest member).2⟩)
      have actual := ClassRequirements.cons first rest
      exact ⟨_, _, actual, actual.verified annotation semantic costs fields inputs⟩

/-- Actual resident tuple edges supply all original forests, without a future input oracle. -/
theorem tuple_inputs (tuple : List (EdgeValue Symbol Guard)) (heap : State Symbol Guard)
    (semantic : SemanticReady heap) (resident : Edges heap tuple) (closed : ClosedEdges tuple) :
    RowsReady heap (tuple.map EdgeValue.children) := by
  intro children member
  obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
  exact ⟨semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge edgeIn), closed edge edgeIn⟩

/-- Every actual column contains only original closed available tuple children. -/
theorem columns_ready (tuple : List (EdgeValue Symbol Guard)) (heap : State Symbol Guard)
    (semantic : SemanticReady heap) (resident : Edges heap tuple) (closed : ClosedEdges tuple) : RowsReady heap (columns tuple) := by
  have inputs := tuple_inputs tuple heap semantic resident closed
  intro column member
  constructor
  · intro value included
    obtain ⟨forest, forestIn, valueIn⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    exact (inputs forest forestIn).1 value valueIn
  · intro value included
    obtain ⟨forest, forestIn, valueIn⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    exact (inputs forest forestIn).2 value valueIn

/-- A completed tuple graph preserves exact heap effects and every requirement operand. -/
theorem Requirements.verified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {tuple : List (EdgeValue Symbol Guard)} {classes : Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Requirements tuple classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) :
    Effects annotation before after ∧ RowsReady after requirements := by
  cases actual with
  | run _ actual =>
      have checked := actual.verified annotation semantic costs fields (tuple_inputs tuple before semantic resident closed)
      refine ⟨checked.1, ?_⟩
      intro row member
      rcases List.mem_append.mp member with column | requirement
      · obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp column
        have original := columns_ready tuple before semantic resident closed original originalIn
        have canonical := canonical_values _ before semantic original.1 original.2
        exact ⟨fun child included => checked.1.keeps.available child (canonical.1 child included), canonical.2⟩
      · exact checked.2 row requirement

/-- A literal equal-arity tuple has finitely many actual requirements after its classes are known. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (tuple : List (EdgeValue Symbol Guard)) (classes : Constraints)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (sameArity : SameArity tuple) :
    ∃ requirements after, Requirements tuple classes before requirements after ∧
      Effects annotation before after ∧ RowsReady after requirements := by
  obtain ⟨requirements, after, actual, _, _⟩ := classes_complete annotation (tuple.map EdgeValue.children) classes before
    semantic costs fields (tuple_inputs tuple before semantic resident closed)
  have completed := Requirements.run sameArity actual
  exact ⟨_, _, completed, completed.verified annotation semantic costs fields resident closed⟩

/-- Tuple requirements retain source column count and each original class occurrence. -/
theorem Requirements.length [DecidableEq (EdgeKey Symbol Guard)]
    {tuple : List (EdgeValue Symbol Guard)} {classes : Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Requirements tuple classes before requirements after) : requirements.length = arity tuple + classes.length := by
  cases actual with
  | run _ actual =>
      rw [List.length_append, List.length_map, actual.length]
      exact congrArg (· + classes.length) (MergedPhysicalGroupEdges.columns_length _ _)

end MicroCFTA.SourceCurrentConjunctionRequirements
