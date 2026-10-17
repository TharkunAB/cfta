import MicroCFTA.SourceCurrentConstrainedCapGuardBinder
import MicroCFTA.SourceCurrentConstrainedCapOriginalSupport
import MicroCFTA.SourceRecursiveIntersectionResultScope

/-!
# Probe freshness from actual source and returned-name support

Original available operands contain only interned free names. Completed
native result scopes contain only intersection names. Both facts exclude
the two callback probe kinds. Interned-name coverage alone does not exclude
them. Literal constructors retain this property through actual readback.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeProbeSupport
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedFacts InternedEdgeResidency InternedBinderProtocol
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
open SourceCurrentConstrainedCapNativeOccurrenceCache (NodeInputs EdgeInputs)
variable {Symbol Guard : Type}

/-- The two source callback probe kinds do not occur in an actual free field. -/
structure ProbeFree (value : Value Symbol Guard) : Prop where
  /-- The literal Depth probe is absent. -/
  depth : .depth ∉ value.free
  /-- Every literal ordinary probe is absent. -/
  ordinary : ∀ level, .uninterned level ∉ value.free

/-- Empty has no callback probe occurrence. -/
theorem empty : ProbeFree (Value.empty (Symbol := Symbol) (Guard := Guard)) :=
  ⟨by simp [Value.free], by intro level; simp [Value.free]⟩

/-- Any literal interned reference satisfies the required probe freshness. -/
theorem interned (name : Nat) : ProbeFree (Value.reference (Symbol := Symbol) (Guard := Guard) (.interned name)) :=
  ⟨by simp [Value.free], by intro level; simp [Value.free]⟩

/-- Any literal recursive pair reference satisfies the same freshness. -/
theorem intersection (first second : Nat) :
    ProbeFree (Value.reference (Symbol := Symbol) (Guard := Guard) (.intersection first second)) :=
  ⟨by simp [Value.free], by intro level; simp [Value.free]⟩

/-- An actual closed free field has no probe occurrence. -/
theorem of_closed (value : Value Symbol Guard) (closed : value.free = []) : ProbeFree value := by
  constructor <;> simp [closed]

/-- Complete original syntax derives freshness from its actual coherent free metadata. -/
theorem of_original (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (original : Original value) (available : Available state value) : ProbeFree value := by
  have names := original.free_interned state facts value available
  constructor
  · intro member
    obtain ⟨_, impossible⟩ := names .depth member
    cases impossible
  · intro level member
    obtain ⟨_, impossible⟩ := names (.uninterned level) member
    cases impossible

/-- Actual returned pair scope excludes both probe kinds without an input-syntax premise. -/
theorem of_scope (pairs : List (Nat × Nat)) (value : Value Symbol Guard) (scope : Scope pairs value) :
    ProbeFree value := by
  constructor
  · intro member
    obtain ⟨_, _, impossible⟩ := scope .depth member
    cases impossible
  · intro level member
    obtain ⟨_, _, impossible⟩ := scope (.uninterned level) member
    cases impossible

/-- Current complete source-request inputs supply freshness for both actual operands. -/
theorem node_inputs (source : State Symbol Guard) (facts : Facts source) (request : NodeRequest Symbol Guard)
    (inputs : NodeInputs source request) : ProbeFree request.left ∧ ProbeFree request.right :=
  ⟨of_original source facts request.left inputs.1 inputs.2.2.1,
    of_original source facts request.right inputs.2.1 inputs.2.2.2.1⟩

/-- Every original child of an actual row request has probe-free source metadata. -/
theorem edge_inputs (source : State Symbol Guard) (facts : Facts source) (request : EdgeRequest Symbol Guard)
    (inputs : EdgeInputs source request) :
    (∀ value ∈ request.left.children, ProbeFree value) ∧
      ∀ value ∈ request.right.children, ProbeFree value := by
  constructor
  · intro value member
    exact of_original source facts value (inputs.1 value member).1 (inputs.1 value member).2.1
  · intro value member
    exact of_original source facts value (inputs.2 value member).1 (inputs.2 value member).2.1

/-- Literal edge readback retains the exact original ordered children's freshness. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : ∀ value ∈ values, Available state value) (fresh : ∀ value ∈ values, ProbeFree value) :
    ∀ value ∈ (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1.children, ProbeFree value := by
  rw [InternedShallowValues.makeEdge_children symbol guard values state facts.coherent facts.cached available]
  exact fresh

/-- Literal node normalization retains only names from surviving original row children. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (fresh : ∀ edge ∈ edges, ∀ value ∈ edge.children, ProbeFree value) :
    ProbeFree (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have names : ∀ name ∈ (run (InternedConstructorTemplates.makeNode edges) state).1.free,
      ∃ edge ∈ edges, ∃ child ∈ edge.children, name ∈ child.free := by
    intro name member
    rw [InternedNormalizationFree.makeNode_free edges state facts.coherent facts.linked resident, childFree_member] at member
    obtain ⟨child, included, named⟩ := member
    obtain ⟨edge, selected, inside⟩ := List.mem_flatMap.mp included
    exact ⟨edge, (List.mem_filter.mp (canonicalEdges_member _ edge selected)).1, child, inside, named⟩
  constructor
  · intro member
    obtain ⟨edge, included, child, inside, named⟩ := names .depth member
    exact (fresh edge included child inside).depth named
  · intro level member
    obtain ⟨edge, included, child, inside, named⟩ := names (.uninterned level) member
    exact (fresh edge included child inside).ordinary level named

/-- Actual union normalization retains only free names from its available original members. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (available : ∀ value ∈ values, Available state value) (fresh : ∀ value ∈ values, ProbeFree value) :
    ProbeFree (run (InternedConstructorTemplates.makeUnion values) state).1 := by
  have names := InternedNormalizationFree.makeUnion_free values state normal.facts.coherent
    normal.facts.cached normal.facts.linked normal.live available
  constructor
  · intro member
    obtain ⟨value, included, named⟩ := (names .depth).mp member
    exact (fresh value included).depth named
  · intro level member
    obtain ⟨value, included, named⟩ := (names (.uninterned level)).mp member
    exact (fresh value included).ordinary level named

/-- A literal completed optional binder cannot introduce a probe into its returned free field. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (context : InternedFreshOrdinaryContext.Context state environment)
    (available : Available state body) (fresh : ProbeFree body) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after) : ProbeFree value := by
  have names := SourceRecursiveIntersectionMaybeMu.free_support pair body state context available value after actual
  exact ⟨fun member => fresh.depth (names .depth member).1,
    fun level member => fresh.ordinary level (names (.uninterned level) member).1⟩

/-- The initial local support discharges both binder freshness checks and is retained at the actual return. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready state) (available : Available state body)
    (bounded : SourceCurrentConstrainedCap.Cap annotation depth body)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation state)
    (weight : Reference → Nat) (bound : Nat) (positive : 0 < bound)
    (oldWeight : weight (.intersection pair.1 pair.2) = bound)
    (classified : SourceCurrentConstrainedCapPairOccurrences.Classified weight bound body) (fresh : ProbeFree body) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after ∧
      SourceCurrentConstrainedCap.Cap annotation depth value ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified weight bound value ∧
      SourceCurrentConstrainedCapGuardHeap.Heap annotation after ∧
      SourceCurrentHereditaryConstruction.MuStored annotation after ∧ Available after value ∧
      SourceEqualityRequiredCache.Keeps state after ∧ ProbeFree value := by
  obtain ⟨value, after, actual, capped, ranked, retained, stored, output, keeps⟩ :=
    SourceCurrentConstrainedCapGuardBinder.complete annotation depth pair body state ready available bounded guards
      weight bound positive oldWeight classified fresh.depth fresh.ordinary
  exact ⟨value, after, actual, capped, ranked, retained, stored, output, keeps,
    optionalBinder pair body state ready.semantic.1 available fresh value after actual⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeProbeSupport
