import MicroCFTA.SourceEqualityProjectionLanguage
import MicroCFTA.SourceEqualityProjectionWorkerComplete
import MicroCFTA.SourceEqualityRequiredExecution

/-!
# General closed getPath execution and accepted-term inclusion

Original source construction derives finite stable projection and its
language inclusion law. Forest root projection has exact union language.
The other forest paths select their original accepted child terms.
-/
namespace MicroCFTA.SourceEqualityProjectionAPI
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityProjectionWorker SourceEqualityProjectionWorkerSound SourceEqualityProjectionWorkerComplete
open SourceEqualityRequiredWorker (Result)
open SourceEqualityRequiredWorkerComplete (StableRun)
open InternedGuardedLanguage (meaning)

/-- Complete node graphs and successful bounded source executions agree in both directions. -/
theorem node_execution_iff [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) :
    Project path value before result after ↔ ∃ fuel readFuel, project fuel readFuel path value before = .done result after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, stable⟩ := node_stable trace
    exact ⟨fuel, readFuel, stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, done⟩
    exact project_graph fuel readFuel path value before result after done

/-- Complete forest graphs and successful bounded source executions agree in both directions. -/
theorem forest_execution_iff [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) :
    Forest path values before result after ↔ ∃ fuel readFuel, forest fuel readFuel path values before = .done result after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, stable⟩ := forest_stable trace
    exact ⟨fuel, readFuel, stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, done⟩
    exact forest_graph fuel readFuel path values before result after done

/-- Complete node projections have one result and complete returned cache. -/
theorem node_unique [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value first second : Value Symbol Guard} {before afterFirst afterSecond : State Symbol Guard}
    (left : Project path value before first afterFirst) (right : Project path value before second afterSecond) :
    first = second ∧ afterFirst = afterSecond :=
  SourceEqualityRequiredExecution.stable_unique (node_stable left) (node_stable right)

/-- Complete forest projections have one result and complete returned cache. -/
theorem forest_unique [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {first second : Value Symbol Guard} {before afterFirst afterSecond : State Symbol Guard}
    (left : Forest path values before first afterFirst) (right : Forest path values before second afterSecond) :
    first = second ∧ afterFirst = afterSecond :=
  SourceEqualityRequiredExecution.stable_unique (forest_stable left) (forest_stable right)

/-- Forest root projection accepts exactly the union of the original operand languages. -/
theorem forest_root [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest [] values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∀ holds ambient term, meaning holds ambient result term ↔ ∃ value ∈ values, meaning holds ambient value term := by
  cases trace with
  | root union => exact (union.verified semantic available closed).2.2.2.2

/-- Proper forest paths retain each selected subterm of an accepted original child forest. -/
theorem forest_included [DecidableEq (EdgeKey Symbol Guard)]
    {index : Int} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest (index :: path) values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) (index :: path) = some part) : meaning holds ambient result part := by
  rw [SourceEqualityNeededMeaning.lookup_cons] at selected
  obtain ⟨term, termAt, partAt⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨value, valueAt, valueAccepted⟩ := SourceEqualityProjectionLanguage.all₂_signed accepted index term termAt
  cases trace with
  | missing absent => rw [absent] at valueAt; cases valueAt
  | selected found body =>
      have same := Option.some.inj (found.symm.trans valueAt)
      subst value
      exact SourceEqualityProjectionLanguage.node body semantic (available _ (select_member found))
        (closed _ (select_member found)) holds ambient term part valueAccepted partAt

/-- Any completed source run derives cache effects and accepted-subterm inclusion. -/
theorem node_done [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat)
    (path : List Int) (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (done : project fuel readFuel path value before = .done result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] ∧
      ∀ holds ambient term part, meaning holds ambient value term → SymbolicSignedPaths.lookup term path = some part → meaning holds ambient result part := by
  have trace := project_graph fuel readFuel path value before result after done
  have checked := SourceEqualityProjectionEffects.node trace semantic available closed
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2,
    SourceEqualityProjectionLanguage.node trace semantic available closed⟩

/-- Original closed source construction derives finite stable execution and its source-language inclusion. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard) (path : List Int) :
    ∃ value before result after, InternedFreshOrdinaryConstruction.build expression [] empty = .done value before ∧
      Project path value before result after ∧ Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] ∧
      StableRun (fun fuel readFuel => project fuel readFuel path value before) result after ∧
      ∀ holds ambient term part, InternedGuardedSyntax.evaluate holds [] expression term →
        SymbolicSignedPaths.lookup term path = some part → meaning holds ambient result part := by
  obtain ⟨value, before, result, after, built, trace, keeps, semantic, available, closed⟩ := SourceEqualityProjectionComplete.source expression path
  refine ⟨value, before, result, after, built, trace, keeps, semantic, available, closed, node_stable trace, ?_⟩
  intro holds ambient term part accepted selected
  apply SourceEqualityProjectionLanguage.node trace (SourceEqualityRequiredSemanticCache.constructed expression value before built)
    ((InternedFreshOrdinaryFacts.closed_verified expression).result value before built)
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value before built) holds ambient term part _ selected
  simpa only [InternedGuardedExecution.closed_language expression value before built holds ambient] using accepted

end MicroCFTA.SourceEqualityProjectionAPI
