import MicroCFTA.SourceSynthesisUniversePrefixConstruction
import MicroCFTA.InternedFreshOrdinaryFirstOrderHeap

/-!
# Prepared heaps from original synthesis construction

The actual universe binder preserves depth-zero stored Mu bodies.
Source-order ordinary and union prefixes preserve the same heap property.
Original signed requests therefore derive preparation from the empty heap.
This result does not establish a native machine execution or a driver bound.
-/
namespace MicroCFTA.SourceSynthesisUniversePrepared
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedShallowHeap
open SourceSynthesisTypeSyntax

section Generic
variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- The actual universe constructor preserves every stored body's depth-zero property. -/
theorem allTypes_shallow (top : Guard) (catalog : List (String × Nat))
    (state : State String Guard) (facts : Facts state) (shallow : Shallow state) :
    Shallow (InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] state).state := by
  exact InternedFreshOrdinaryFirstOrderHeap.binder_shallow true (allTypesBody top catalog)
    (SourceSynthesisUniverseNativeInput.allTypesBody_binderFree top catalog) [] state facts
    (by intro value member; cases member) shallow (by intro value member; cases member)

private def Preserves (expression : Syntax String Guard) : Prop :=
  ∀ state, Facts state → Shallow state →
    Shallow (InternedFreshOrdinaryConstruction.build expression [] state).state

omit [DecidableEq (EdgeKey String Guard)] in
private theorem bind_shallow (outcome : Outcome String Guard First)
    (next : First → State String Guard → Outcome String Guard Result)
    (first : Shallow outcome.state)
    (later : ∀ value after, outcome = .done value after → Shallow after →
      Shallow (next value after).state) : Shallow (outcome.bind next).state := by
  cases outcome with
  | pending => exact first
  | done value after => exact later value after rfl first

private theorem many_shallow (expressions : List (Syntax String Guard)) :
    (∀ expression ∈ expressions, Preserves expression) → ∀ state, Facts state → Shallow state →
      Shallow (InternedFreshOrdinaryConstruction.buildMany expressions [] state).state := by
  induction expressions with
  | nil =>
      intro _ state _ shallow
      simpa only [InternedFreshOrdinaryConstruction.buildMany, Outcome.state] using shallow
  | cons first rest ih =>
      intro checked state facts shallow
      rw [InternedFreshOrdinaryConstruction.buildMany]
      apply bind_shallow _ _ (checked first List.mem_cons_self state facts shallow)
      intro value after done afterShallow
      have verified := InternedFreshOrdinaryFacts.build_verified first [] state facts
        (by intro item member; cases member)
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
      apply bind_shallow _ _
        (ih (fun expression member => checked expression (List.mem_cons_of_mem _ member)) after afterFacts afterShallow)
      intro values final _ finalShallow
      exact finalShallow

private theorem edges_shallow (rows : List (EdgeSyntax String Guard)) :
    (∀ row ∈ rows, match row with
      | .mk _ _ children => ∀ child ∈ children, Preserves child) →
      ∀ state, Facts state → Shallow state →
        Shallow (InternedFreshOrdinaryConstruction.buildEdges rows [] state).state := by
  induction rows with
  | nil =>
      intro _ state _ shallow
      simpa only [InternedFreshOrdinaryConstruction.buildEdges, Outcome.state] using shallow
  | cons first rest ih =>
      cases first with
      | mk symbol constraint children =>
          intro checked state facts shallow
          rw [InternedFreshOrdinaryConstruction.buildEdges]
          apply bind_shallow _ _
            (many_shallow children (checked _ List.mem_cons_self) state facts shallow)
          intro values after done afterShallow
          have verified := InternedFreshOrdinaryFacts.buildMany_verified children [] state facts
            (by intro item member; cases member)
          have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
          have available := verified.result values after done
          have edgeVerified := edge_verified symbol constraint values after afterFacts available
          have madeShallow : Shallow (work (makeEdge symbol constraint values) after).state := by
            intro key entry body depth ordinary stored
            exact afterShallow key entry body depth ordinary stored
          apply bind_shallow (work (makeEdge symbol constraint values) after) _ madeShallow
          intro edge afterEdge edgeDone edgeShallow
          have edgeFacts : Facts afterEdge := by
            simpa only [edgeDone, Outcome.state] using edgeVerified.facts
          apply bind_shallow _ _
            (ih (fun row member => checked row (List.mem_cons_of_mem _ member)) afterEdge edgeFacts edgeShallow)
          intro edges final _ finalShallow
          exact finalShallow

end Generic

open SourceSynthesisFirstOrderConstruction (Expression Row)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisUniverseOrigins (OverUniverse)
variable [DecidableEq (EdgeKey String Guard)]

/-- Every actual prefix outcome retains depth-zero bodies, including pending outcomes. -/
theorem overUniverse_shallow (catalog : List (String × Nat)) (expression : Expression)
    (origin : OverUniverse (allTypes top catalog) expression) :
    ∀ state, Facts state → Shallow state →
      Shallow (InternedFreshOrdinaryConstruction.build expression [] state).state := by
  change Preserves expression
  induction origin with
  | atom => exact allTypes_shallow top catalog
  | node rows _ checked =>
      intro state facts shallow
      rw [InternedFreshOrdinaryConstruction.build]
      apply bind_shallow _ _ (edges_shallow rows (by
        intro row member
        cases row
        exact checked _ member) state facts shallow)
      intro values after _ afterShallow
      exact shallow_preserved after _ afterShallow (makeNode_noNewMu values after)
  | union members _ checked =>
      intro state facts shallow
      rw [InternedFreshOrdinaryConstruction.build]
      apply bind_shallow _ _ (many_shallow members checked state facts shallow)
      intro values after _ afterShallow
      exact shallow_preserved after _ afterShallow (makeUnion_noNewMu values after)

/-- Complete empty-cache prefix construction derives its stored-body preparation. -/
theorem overUniverse_prepared (catalog : List (String × Nat)) (expression : Expression)
    (origin : OverUniverse (allTypes top catalog) expression) :
    ∃ value final, InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ Shallow final ∧ MergedPhysicalWarmup.Prepared final ∧
      SourceSynthesisUniversePrefixHeight.height value ≤ sizeOf expression := by
  obtain ⟨value, final, _pick, done, facts, available, _ready, _allowed, bounded⟩ :=
    SourceSynthesisUniversePrefixConstruction.overUniverse_prefix_bound catalog expression origin
  have shallow : Shallow final := by
    have retained := overUniverse_shallow catalog expression origin empty empty_facts empty_shallow
    simpa only [done, Outcome.state] using retained
  exact ⟨value, final, done, facts, available, shallow,
    MergedPhysicalWarmup.prepared_of_shallow final facts shallow, bounded⟩

/-- Original library/query requests derive preparation without a caller heap invariant. -/
theorem firstOrderRaw_prepared (lib : Library) (query : Query) (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ value final, InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
          Facts final ∧ Available final value ∧ Shallow final ∧ MergedPhysicalWarmup.Prepared final ∧
          SourceSynthesisUniversePrefixHeight.height value ≤ sizeOf expression := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression =>
      exact overUniverse_prepared _ expression
        (SourceSynthesisUniverseOrigins.firstOrderRaw_overUniverse lib query size expression returned)

end MicroCFTA.SourceSynthesisUniversePrepared
